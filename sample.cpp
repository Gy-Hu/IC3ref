#include <iostream>

#include "Solver.h"
#include "Graph.h"
#include "clausebuf.h"
#include "ts.h"

extern "C" {
#include "aiger.h"
}

void printHelpMessage (const char * argv0) {
    std::cout << "Usage: " << argv0 << "[options] aiger\n" ;
    std::cout << "Options: \n" ;
    std::cout << "          -f inv.cnf : load frame for cex sampling\n" ;
    std::cout << "          -g graph   : dump graph to graph \n" ;
    std::cout << "          -i in.cnf out.cnf: load frame for filtering \n" ;
    std::cout << "          -c output.cnf : generate CTIs and corresponding clauses\n" ;
    std::cout << "          -h : print help message \n" ;
}

int main(int argc, char ** argv) {

  const char * fname = NULL;
  const char * framebuf = NULL;
  const char * dump_graph = NULL;
  const char * outframebuf = NULL;
  const char * clause_output = NULL;
  bool sampling_cex = false;
  bool filtering_frame = false;
  bool generate_clauses = false;

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
    auto ret = sample_cti(ts, 100, m);
    std::cout << "Total samples: "<< ret << std::endl;
    // sample model: P /\ T /\ neg P'
    
    // If clause generation is requested, generate and save clauses
    if (generate_clauses && ret > 0) {
      ClauseBuf cti_clauses;
      
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
          
          // Add literal to clause (positive if true, negative if false)
          clause.push_back(is_true ? var_id : -var_id);
        }
        
        // Add clause if not empty
        if (!clause.empty()) {
          cti_clauses.clauses.push_back(clause);
        }
      }
      
      // Save clauses to output file
      cti_clauses.dump(clause_output);
      std::cout << "Wrote " << cti_clauses.clauses.size() << " CTI clauses to " << clause_output << std::endl;
    }
  }
  
  aiger_reset(aig);
  return 0;
}
