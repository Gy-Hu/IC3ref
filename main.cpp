/*********************************************************************
Copyright (c) 2013, Aaron Bradley

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/

#include <iostream>
#include <string>
#include <time.h>

extern "C" {
#include "aiger.h"
}
#include "IC3.h"
#include "Model.h"


static void print_usage() {
  std::cout
    << "IC3: Reference implementation of IC3" << std::endl
    << std::endl
    << "Usage:" << std::endl
    << "  ./IC3 [<option>|<property ID>]* < <AIGER file>" << std::endl
    << "  ./IC3 --extract-features <frames> <input.aig> <output.json>" << std::endl
    << std::endl
    << "Options:" << std::endl
    << "  -v                Enable verbose output" << std::endl
    << "  -s                Print runtime statistics" << std::endl
    << "  -r                Randomize execution" << std::endl
    << "  -b                Use basic generalization" << std::endl
    << "  -h, --help        Show this help message" << std::endl
    << std::endl
    << "Notes:" << std::endl
    << "  - In default mode IC3 reads the AIGER model from stdin." << std::endl
    << "  - In feature-extraction mode IC3 reads from the provided input file and writes features to the JSON file." << std::endl;
}

int main(int argc, char ** argv) {
  unsigned int propertyIndex = 0;
  bool basic = false, random = false;
  int verbose = 0;
  int feature_extraction_frame_limit = 0; // New variable for feature extraction mode
  string input_file = "";  // Input AIG file for feature extraction mode
  string output_file = ""; // Output JSON file for feature extraction mode
  for (int i = 1; i < argc; ++i) {
    string arg = string(argv[i]);
    if (arg == "-v")
      // option: verbosity
      verbose = 2;
    else if (arg == "-s")
      // option: print statistics
      verbose = max(1, verbose);
    else if (arg == "-r") {
      // option: randomize the run, which is useful in performance
      // testing; default behavior is deterministic
      srand(time(NULL));
      random = true;
    }
    else if (arg == "-b")
      // option: use basic generalization
      basic = true;
    else if (arg == "-h" || arg == "--help") {
      print_usage();
      return 0;
    }
    else if (arg == "--extract-features") {
      // New option: enable feature extraction mode
      if (i + 3 < argc) {
        feature_extraction_frame_limit = (unsigned) atoi(argv[++i]);
        if (feature_extraction_frame_limit <= 0) {
            cout << "Error: Number of frames for --extract-features must be positive." << endl;
            return 1;
        }
        input_file = string(argv[++i]);
        output_file = string(argv[++i]);
      } else {
        cout << "Error: --extract-features requires 3 arguments: <frames> <input.aig> <output.json>" << endl;
        return 1;
      }
    }
    else
      // optional argument: set property index
      propertyIndex = (unsigned) atoi(argv[i]);
  }

  // read AIGER model
  aiger * aig = aiger_init();
  const char * msg;
  if (feature_extraction_frame_limit > 0) {
    // In feature extraction mode, read from specified file
    msg = aiger_open_and_read_from_file(aig, input_file.c_str());
  } else {
    // In normal mode, read from stdin
    msg = aiger_read_from_file(aig, stdin);
  }
  if (msg) {
    cout << msg << endl;
    return 0;
  }
  // create the Model from the obtained aig
  Model * model = modelFromAiger(aig, propertyIndex);
  aiger_reset(aig);
  if (!model) return 0;

  // model check it
  bool rv = IC3::check(*model, verbose, basic, random, feature_extraction_frame_limit, output_file); // Pass new parameters
  // print 0/1 according to AIGER standard
  // Suppress normal output in feature extraction mode
  if (feature_extraction_frame_limit == 0) {
      cout << !rv << endl;
  }

  delete model;

  return 1;
}
