#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <map>
#include <vector>
#include <iomanip>
#include <set>
#include <climits>
#include <algorithm>

#include "Solver.h"
#include "Graph.h"
#include "clausebuf.h"
#include "ts.h"

extern "C" {
#include "aiger.h"
}

// Simple JSON string escape function
std::string jsonEscape(const std::string& s) {
    std::ostringstream o;
    for (auto c = s.cbegin(); c != s.cend(); c++) {
        if (*c == '"' || *c == '\\' || ('\x00' <= *c && *c <= '\x1f')) {
            o << "\\u" << std::hex << std::setw(4) << std::setfill('0') << static_cast<int>(*c);
        } else {
            o << *c;
        }
    }
    return o.str();
}

// Convert clause to integer set for subset checking
std::set<int> clauseToSet(const std::vector<int>& clause) {
    std::set<int> result;
    for (int lit : clause) {
        result.insert(abs(lit)); // Use absolute value, only care about variables, not polarity
    }
    return result;
}

// Check if one set is a subset of another
bool isSubset(const std::set<int>& subset, const std::set<int>& superset) {
    return std::includes(superset.begin(), superset.end(), subset.begin(), subset.end());
}

// Check if inv clause literals are subset of CTI clause literals with polarity consideration
bool isClauseSubsetWithPolarity(const std::vector<int>& inv_clause, const std::vector<int>& cti_clause) {
    // Convert CTI clause to a set for fast lookup
    std::set<int> cti_literals;
    for (int lit : cti_clause) {
        cti_literals.insert(lit);
        // Add both polarity versions for each variable to match Python implementation
        // In this encoding: even numbers (2,4,6...) are positive literals, odd numbers (3,5,7...) are negative
        if (lit % 2 == 0) { // Even number: positive literal (v1, v2, etc.)
            cti_literals.insert(lit + 1); // Add negative version
        } else { // Odd number: negative literal (~v1, ~v2, etc.)
            cti_literals.insert(lit - 1); // Add positive version
        }
    }
    
    // Check if all literals in inv_clause are in cti_literals
    for (int lit : inv_clause) {
        if (cti_literals.find(lit) == cti_literals.end()) {
            return false;
        }
    }
    return true;
}

// Calculate the number of literals in a clause
size_t clauseSize(const std::string& clause_str) {
    size_t count = 1; // At least one literal
    for (char c : clause_str) {
        if (c == ' ') count++;
    }
    return count;
}

void printHelpMessage (const char * argv0) {
    std::cout << "Usage: " << argv0 << "[options] aiger\n" ;
    std::cout << "Options: \n" ;
    std::cout << "          -f inv.cnf : load frame for cex sampling\n" ;
    std::cout << "          -g graph   : dump graph to graph \n" ;
    std::cout << "          -i in.cnf out.cnf: load frame for filtering \n" ;
    std::cout << "          -c output.cnf : generate CTIs and corresponding clauses\n" ;
    std::cout << "          -m mapping.json : generate mapping from CTI clauses to invariant clauses\n" ;
    std::cout << "          -h : print help message \n" ;
}

int main(int argc, char ** argv) {

  const char * fname = NULL;
  const char * framebuf = NULL;
  const char * dump_graph = NULL;
  const char * outframebuf = NULL;
  const char * clause_output = NULL;
  const char * mapping_output = NULL;
  bool sampling_cex = false;
  bool filtering_frame = false;
  bool generate_clauses = false;
  bool generate_mapping = false;

  if (argc > 1) {
    int idx = 1;
    for (; idx < argc - 1 ; ++ idx) {
      if(argv[idx] == std::string("-f")) {
        framebuf = argv[++idx];
        sampling_cex = true;
      } else if (argv[idx] == std::string("-g"))
        dump_graph = argv[++idx];
      else if (argv[idx] == std::string("-i")) {
        framebuf = argv[++idx];
        outframebuf = argv[++idx];
        filtering_frame = true;
      }
      else if (argv[idx] == std::string("-c")) {
        clause_output = argv[++idx];
        generate_clauses = true;
      }
      else if (argv[idx] == std::string("-m")) {
        mapping_output = argv[++idx];
        generate_mapping = true;
      }
      else if (argv[idx] == std::string("-h")) {
        printHelpMessage(argv[0]);
        return 0;
      }
      else {
        std::cout << "unknown option:" << argv[idx] << std::endl;
        printHelpMessage(argv[0]);
        return 1;
      }
    }
    if (idx != argc - 1) {
      printHelpMessage(argv[0]);
      return 1;
    }
    fname = argv[argc-1];
  } else {
    printHelpMessage(argv[0]);
    return 1;
  }

  // read AIGER model
  aiger * aig = aiger_init();
  const char * msg;
  msg = aiger_open_and_read_from_file(aig, fname);

  if (msg) {
    std::cout << msg << std::endl;
    return 1;
  }

  if (dump_graph) {
    Graph model (aig);
    model.dump(dump_graph);
  }
  // construct AIG -> graph
  // sample model: P /\ T /\ neg P'
  // do : generalize predecessor
  // load inv.cnf and find it?

  // construct transition relation
  if(filtering_frame) {
    ClauseBuf buf, bufout;
    buf.from_file(framebuf);

    TransitionSystem ts(aig, 0);

    std::cout << "Loaded " << buf.clauses.size() << " clauses from " << framebuf << std::endl;
    std::cout << "Loaded TS (SV: " << ts.statevars().size() << " IV:" << ts.inputvars().size() << " ) from "  << fname << std::endl;
    if(is_ts_trivially_unsafe(ts)) {
      std::cout << "TS is trivially unsafe! Will not filter clauses." << std::endl;
      return 1;
    }

    filter_clauses(buf, bufout, ts);
    bufout.dump(outframebuf);

    std::cout << "Write " << bufout.clauses.size() << " clauses to " << outframebuf << std::endl;
    aiger_reset(aig);
    return 0;
  }

  if(sampling_cex) {
    TransitionSystem ts(aig, 0);
    std::vector<ctiModel> m;
    // Print the AIGER encoding formula for reference
    std::cout << "=== State Variable to AIGER Literal Conversion Formula ===" << std::endl;
    std::cout << "For state variable stateN:" << std::endl;
    std::cout << "  If value is 0 (False): AIGER literal = 2*(1+num_inputs+N) + 1 (odd number)" << std::endl;
    std::cout << "  If value is 1 (True): AIGER literal = 2*(1+num_inputs+N) (even number)" << std::endl;
    std::cout << "Number of inputs in this model: " << aig->num_inputs << std::endl;
    std::cout << "Number of latches in this model: " << aig->num_latches << std::endl;
    std::cout << "============================================" << std::endl;
    
    auto ret = sample_cti(ts, 100, m);
    std::cout << "Total samples: "<< ret << std::endl;
    // sample model: P /\ T /\ neg P'
    
    // If clause generation is requested, generate and save clauses
    if ((generate_clauses || generate_mapping) && ret > 0) {
      ClauseBuf cti_clauses;
      
      // Use map to store mapping relationship
      std::map<std::string, std::vector<std::string>> mapping;
      
      // For storing all CTI clauses and INV clauses set representations, avoid recalculation
      std::map<std::string, std::set<int>> cti_clause_sets;
      std::map<std::string, std::set<int>> inv_clause_sets;
      
      // For keeping the minimal subset for each CTI
      std::map<std::string, std::vector<std::pair<std::string, size_t>>> min_subsets;
      
      // Map for storing human-readable CTI to inv clause mapping
      std::map<std::string, std::vector<std::string>> human_readable_mapping;
      
      // First load invariant clauses, pre-compute their set representations
      std::vector<std::vector<int>> inv_clauses;
      std::vector<std::string> inv_clauses_str;
      
      if (generate_mapping && framebuf != NULL) {
        ClauseBuf inv_buf;
        inv_buf.from_file(framebuf);
        
        for (const auto& inv_clause : inv_buf.clauses) {
          std::string inv_clause_str;
          for (size_t i = 0; i < inv_clause.size(); i++) {
            if (i > 0) inv_clause_str += " ";
            inv_clause_str += std::to_string(inv_clause[i]);
          }
          
          inv_clauses.push_back(inv_clause);
          inv_clauses_str.push_back(inv_clause_str);
          inv_clause_sets[inv_clause_str] = clauseToSet(inv_clause);
        }
        
        std::cout << "Loaded " << inv_clauses.size() << " invariant clauses for mapping" << std::endl;
      }
      
      // Generate clauses from CTI models
      for (const auto& model : m) {
        // Vector to store AIGER latch literals - using same logic as in mapping generation
        std::vector<unsigned int> aiger_literals;
        
        // Create a string representation of the CTI in original state format
        std::string cti_state_str;
        std::vector<std::string> state_vars;
        std::vector<std::string> state_vals;
        
        // For human-readable CTI representation
        std::string human_readable_cti;
        
        for (size_t i = 0; i < model.vars.size(); i++) {
          std::string var_name = model.vars[i]->to_string();
          bool is_true = (model.vals[i]->to_string() == "true");
          
          // Add to state variables and values arrays for display
          if (var_name.find("state") == 0) {
            state_vars.push_back(var_name);
            state_vals.push_back(is_true ? "1" : "0");
          }
          
          // Map the state variable to its corresponding AIGER latch literal
          if (var_name.find("state") == 0) {
            // Extract state index
            int state_idx = std::stoi(var_name.substr(5));
            
            // Skip if not a valid state variable
            if (state_idx >= aig->num_latches) continue;
            
            // Calculate AIGER latch literal (even number for positive)
            unsigned int aiger_latch_id = 2 * (1 + aig->num_inputs + state_idx);
            
            // Apply polarity based on state value - same logic as in mapping
            // If state is true (1), use even number (positive literal)
            // If state is false (0), use odd number (negative literal) 
            unsigned int aiger_literal = is_true ? aiger_latch_id : aiger_latch_id + 1;
            
            // Removed detailed conversion prints
            
            // Add to our list of literals for this CTI
            aiger_literals.push_back(aiger_literal);
            
            // Add to human-readable CTI representation
            if (!human_readable_cti.empty()) human_readable_cti += " ";
            human_readable_cti += var_name + "=" + (is_true ? "1" : "0");
          }
        }
        
        // Construct the CTI string in the format shown in the console output
        for (size_t i = 0; i < state_vars.size(); i++) {
          if (i > 0) cti_state_str += " ";
          cti_state_str += state_vars[i];
        }
        cti_state_str += "\n";
        for (size_t i = 0; i < state_vals.size(); i++) {
          if (i > 0) cti_state_str += "       ";
          cti_state_str += state_vals[i];
        }
        
        // Add clause if not empty - use the same literals as in mapping.json keys
        if (!aiger_literals.empty()) {
          // Sort literals to ensure consistency
          std::sort(aiger_literals.begin(), aiger_literals.end());
          
          // Convert to a regular clause format
          std::vector<int> clause;
          for (unsigned int lit : aiger_literals) {
            clause.push_back(lit);
          }
          
          cti_clauses.clauses.push_back(clause);
          
          // If mapping generation is needed, add this clause to the mapping
          if (generate_mapping && framebuf != NULL) {
            // Convert clause to string representation for use as key in the mapping
            std::string clause_str;
            for (size_t i = 0; i < clause.size(); i++) {
              if (i > 0) clause_str += " ";
              clause_str += std::to_string(clause[i]);
            }
            
            // Use CTI state string as the key in mapping instead of clause_str
            std::string mapping_key = cti_state_str;
            
            // Calculate CTI clause set representation
            std::set<int> cti_set = clauseToSet(clause);
            cti_clause_sets[clause_str] = cti_set;
            
            // Initialize minimal subset record
            min_subsets[clause_str] = std::vector<std::pair<std::string, size_t>>();
            
            // Bottom-up matching: find inv clauses that are subsets of variables in CTI clause
            // Stop at the first match (scanning from bottom up)
            bool match_found = false;
            for (int i = inv_clauses.size() - 1; i >= 0 && !match_found; i--) {
              const auto& inv_clause = inv_clauses[i];
              const auto& inv_clause_str = inv_clauses_str[i];
              
              // Check with original set-based check
              if (isSubset(inv_clause_sets[inv_clause_str], cti_set)) {
                // Found subset, record it and stop searching
                min_subsets[clause_str].push_back(std::make_pair(inv_clause_str, inv_clause_sets[inv_clause_str].size()));
                match_found = true;
              }
              // Additional check with polarity if no match found yet
              else if (!match_found && isClauseSubsetWithPolarity(inv_clause, clause)) {
                // Found subset considering polarity, record it and stop searching
                min_subsets[clause_str].push_back(std::make_pair(inv_clause_str, inv_clause.size()));
                match_found = true;
              }
            }
            
            // If subsets found, include all valid subsets, not just the smallest ones
            if (!min_subsets[clause_str].empty()) {
              // Sort by size for consistency (smaller clauses first)
              std::sort(min_subsets[clause_str].begin(), min_subsets[clause_str].end(), 
                  [](const std::pair<std::string, size_t>& a, const std::pair<std::string, size_t>& b) {
                    return a.second < b.second;
                  });
              
              // Include all valid subsets, not just the smallest ones
              std::vector<std::string> valid_subsets;
              for (const auto& subset : min_subsets[clause_str]) {
                valid_subsets.push_back(subset.first);
              }
              
              // Update mapping with all valid subsets, using CTI state string as key
              mapping[mapping_key] = valid_subsets;
              
              // Also update human-readable mapping
              human_readable_mapping[human_readable_cti] = valid_subsets;
              
              std::cout << "Mapped CTI: " << human_readable_cti << " to clause: " << valid_subsets[0] << std::endl;
            }
          }
        }
      }
      
      // Save clauses to output file
      if (generate_clauses) {
        cti_clauses.dump(clause_output);
        std::cout << "Wrote " << cti_clauses.clauses.size() << " CTI clauses to " << clause_output << std::endl;
      }
      
      // Save mapping to JSON file
      if (generate_mapping) {
        std::ofstream json_file(mapping_output);
        if (json_file.is_open()) {
          // Create mapping with actual AIGER latch IDs as keys
          std::map<std::string, std::vector<std::string>> formatted_mapping;
          
          // Process each CTI model
          for (const auto& model : m) {
            // Vector to store transformed AIGER latch IDs with polarity
            std::vector<unsigned int> aiger_literals;
            std::string cti_state_description = "";
            
            // Process state variables - transform to AIGER latch literals
            for (size_t i = 0; i < model.vars.size(); i++) {
              std::string var_name = model.vars[i]->to_string();
              bool is_true = (model.vals[i]->to_string() == "true");
              
              // Add to state description for debugging/logging
              if (var_name.find("state") == 0) {
                if (!cti_state_description.empty()) cti_state_description += " ";
                cti_state_description += var_name + "=" + (is_true ? "1" : "0");
                
                // Store state variable and value for human-readable output
                if (!cti_state_description.empty()) {
                  // std::cout << "CTI State: " << cti_state_description << std::endl;
                }
              }
              
              // Map the state variable to its corresponding AIGER latch literal
              if (var_name.find("state") == 0) {
                // Extract state index
                int state_idx = std::stoi(var_name.substr(5));
                
                // Check if it's a valid state variable
                if (state_idx < aig->num_latches) {
                  // Calculate AIGER latch literal (even number for positive)
                  unsigned int aiger_latch_id = 2 * (1 + aig->num_inputs + state_idx);
                  
                  // Apply polarity based on state value:
                  // If state is false (0), use odd number (negative literal)
                  // If state is true (1), use even number (positive literal)
                  unsigned int aiger_literal = is_true ? aiger_latch_id : aiger_latch_id + 1;
                  
                  // Removed detailed conversion prints
                  
                  // Add to our list of literals for this CTI
                  aiger_literals.push_back(aiger_literal);
                }
              }
            }
            
            // Sort the literals for consistency
            std::sort(aiger_literals.begin(), aiger_literals.end());
            
            // Build the key for mapping (space-separated literals with polarity)
            std::string aiger_key = "";
            for (size_t i = 0; i < aiger_literals.size(); i++) {
              if (i > 0) aiger_key += " ";
              aiger_key += std::to_string(aiger_literals[i]);
            }
            
            // Find match in invariant clauses (scanning from bottom up)
            if (generate_mapping && framebuf != NULL && !aiger_literals.empty()) {
              bool match_found = false;
              std::string matching_inv = "";
              
              // First, we need to flip the CTI literals to get the clause that blocks this CTI
              // According to De Morgan's law: ~(a & b & c) = ~a | ~b | ~c
              std::vector<unsigned int> flipped_literals;
              for (unsigned int lit : aiger_literals) {
                // Flip each literal: even becomes odd, odd becomes even
                flipped_literals.push_back(lit ^ 1); // XOR with 1 flips the last bit
              }
              
              // Sort the flipped literals
              std::sort(flipped_literals.begin(), flipped_literals.end());
              
              // Construct a human-readable CTI state representation for debugging
              std::string cti_human_readable = "CTI: ";
              for (size_t i = 0; i < model.vars.size(); i++) {
                std::string var_name = model.vars[i]->to_string();
                bool is_true = (model.vals[i]->to_string() == "true");
                
                if (var_name.find("state") == 0) {
                  if (cti_human_readable.length() > 5) cti_human_readable += ", ";
                  cti_human_readable += var_name + "=" + (is_true ? "1" : "0");
                }
              }
              std::cout << cti_human_readable << std::endl;
              
              // Print the corresponding AIGER literals for debugging
              std::cout << "AIGER literals: ";
              for (unsigned int lit : aiger_literals) {
                std::cout << lit << " ";
              }
              std::cout << std::endl;
              
              // Print the flipped literals that would block this CTI
              std::cout << "Flipped (blocking) literals: ";
              for (unsigned int lit : flipped_literals) {
                std::cout << lit << " ";
              }
              std::cout << std::endl;
              
              // Now check which invariant clause conflicts with this CTI
              // For each invariant clause, check if it conflicts with the CTI state
              for (int i = 0; i < inv_clauses.size() && !match_found; i++) {
                const auto& inv_clause = inv_clauses[i];
                const auto& inv_clause_str = inv_clauses_str[i];
                
                // Check if the invariant clause conflicts with the CTI
                // A clause conflicts with a CTI if all literals in the clause 
                // contradict the corresponding state values in the CTI
                bool clause_conflicts = true;
                
                // std::cout << "Testing inv clause: " << inv_clause_str << std::endl;
                
                // For each literal in inv clause, check if it contradicts the CTI state
                for (int lit : inv_clause) {
                  // For each literal, check if it's in the aiger_literals (not flipped)
                  // If a literal from inv is in aiger_literals, then it doesn't contradict
                  if (std::find(aiger_literals.begin(), aiger_literals.end(), lit) != aiger_literals.end()) {
                    clause_conflicts = false;
                    // std::cout << "  Literal " << lit << " matches CTI state, no conflict" << std::endl;
                    break;
                  }
                  
                  // If a literal from inv is not in flipped_literals, it means it
                  // refers to a variable not in the CTI, so no contradiction
                  if (std::find(flipped_literals.begin(), flipped_literals.end(), lit) == flipped_literals.end()) {
                    clause_conflicts = false;
                    // std::cout << "  Literal " << lit << " not in CTI variables" << std::endl;
                    break;
                  }
                }
                
                if (clause_conflicts) {
                  matching_inv = inv_clause_str;
                  match_found = true;
                  std::cout << "  MATCH FOUND! Clause " << inv_clause_str 
                            << " conflicts with CTI" << std::endl;
                }
              }
              
              if (match_found) {
                std::vector<std::string> mapped_invs;
                mapped_invs.push_back(matching_inv);
                formatted_mapping[aiger_key] = mapped_invs;
              }
            }
          }
          
          // Write out the formatted mapping
          json_file << "{\n";
          
          size_t count = 0;
          for (const auto& map_entry : formatted_mapping) {
            json_file << "  \"" << jsonEscape(map_entry.first) << "\": [";
            for (size_t i = 0; i < map_entry.second.size(); i++) {
              if (i > 0) json_file << ", ";
              json_file << "\"" << jsonEscape(map_entry.second[i]) << "\"";
            }
            json_file << "]";
            
            if (++count < formatted_mapping.size()) {
              json_file << ",";
            }
            json_file << "\n";
          }
          
          json_file << "}\n";
          json_file.close();
          std::cout << "Wrote mapping of " << formatted_mapping.size() << " CTI clauses to invariant clause subsets in " << mapping_output << std::endl;
        } else {
          std::cerr << "Failed to open JSON mapping file for writing: " << mapping_output << std::endl;
        }
      }
    }
  }
  
  aiger_reset(aig);
  return 0;
}

