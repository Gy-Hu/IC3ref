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
    auto ret = sample_cti(ts, 1000, m);
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
        // Extract literals from the model and create a clause
        std::vector<int> clause;
        for (size_t i = 0; i < model.vars.size(); i++) {
          // Get variable ID (assuming it's a number in the variable name)
          std::string var_name = model.vars[i]->to_string();
          int var_id = 0;
          
          // Extract numeric ID from variable name
          if (var_name.find("state") == 0) {
            var_id = std::stoi(var_name.substr(5));
          } else if (var_name.find("v") == 0) {
            var_id = std::stoi(var_name.substr(1));
          }
          
          // Skip if var_id is 0
          if (var_id == 0) continue;
          
          // Determine if the variable is true or false in the model
          bool is_true = false;
          if (model.vals[i]->to_string() == "true") {
            is_true = true;
          }
          
          // Apply De Morgan's Law: negate each literal in the cube to form a clause
          // ¬(a ∧ b ∧ c) = ¬a ∨ ¬b ∨ ¬c
          // If variable is true in the CTI (cube), it should be false in the clause
          // If variable is false in the CTI (cube), it should be true in the clause
          clause.push_back(is_true ? var_id+1 : var_id);
        }
        
        // Add clause if not empty
        if (!clause.empty()) {
          cti_clauses.clauses.push_back(clause);
          
          // If mapping generation is needed, add this clause to the mapping
          if (generate_mapping && framebuf != NULL) {
            // Convert clause to string representation for use as key in the mapping
            std::string clause_str;
            for (size_t i = 0; i < clause.size(); i++) {
              if (i > 0) clause_str += " ";
              clause_str += std::to_string(clause[i]);
            }
            
            // Calculate CTI clause set representation
            std::set<int> cti_set = clauseToSet(clause);
            cti_clause_sets[clause_str] = cti_set;
            
            // Initialize minimal subset record
            min_subsets[clause_str] = std::vector<std::pair<std::string, size_t>>();
            
            // Bottom-up matching: find inv clauses that are subsets of variables in CTI clause
            for (size_t i = 0; i < inv_clauses.size(); i++) {
              const auto& inv_clause = inv_clauses[i];
              const auto& inv_clause_str = inv_clauses_str[i];
              const auto& inv_set = inv_clause_sets[inv_clause_str];
              
              // Check if inv clause is a subset of CTI clause
              if (isSubset(inv_set, cti_set)) {
                // Found subset, record its size
                size_t size = inv_set.size();
                min_subsets[clause_str].push_back(std::make_pair(inv_clause_str, size));
              }
            }
            
            // If subsets found, sort by size and keep only the smallest ones
            if (!min_subsets[clause_str].empty()) {
              // Sort by size
              std::sort(min_subsets[clause_str].begin(), min_subsets[clause_str].end(), 
                  [](const std::pair<std::string, size_t>& a, const std::pair<std::string, size_t>& b) {
                    return a.second < b.second;
                  });
              
              // Find the minimum size
              size_t min_size = min_subsets[clause_str][0].second;
              
              // Keep only subsets with the minimum size
              std::vector<std::string> smallest_subsets;
              for (const auto& subset : min_subsets[clause_str]) {
                if (subset.second == min_size) {
                  smallest_subsets.push_back(subset.first);
                } else {
                  break; // Since already sorted, once size not equal to min, all others won't be equal
                }
              }
              
              // Update mapping with smallest subsets
              mapping[clause_str] = smallest_subsets;
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
          // Manually build simple JSON format
          json_file << "{\n";
          
          size_t count = 0;
          for (const auto& map_entry : mapping) {
            json_file << "  \"" << jsonEscape(map_entry.first) << "\": [";
            for (size_t i = 0; i < map_entry.second.size(); i++) {
              if (i > 0) json_file << ", ";
              json_file << "\"" << jsonEscape(map_entry.second[i]) << "\"";
            }
            json_file << "]";
            
            if (++count < mapping.size()) {
              json_file << ",";
            }
            json_file << "\n";
          }
          
          json_file << "}\n";
          json_file.close();
          std::cout << "Wrote mapping of " << mapping.size() << " CTI clauses to minimal invariant clause subsets in " << mapping_output << std::endl;
        } else {
          std::cerr << "Failed to open JSON mapping file for writing: " << mapping_output << std::endl;
        }
      }
    }
  }
  
  aiger_reset(aig);
  return 0;
}
