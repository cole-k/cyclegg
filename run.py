import os 

output_dir = "progress-heuristics"
time_limit = 600


command = "/Users/pro/.cargo/bin/cargo run --package cyclegg --bin cyclegg --release -- examples/isaplanner.ceg -d 100000 -t %d -r --only-generalize > %s" % (time_limit, os.path.join("results", output_dir, "output-isa"))
os.system(command)
os.system("cp target/results.csv %s" % os.path.join("results", output_dir, "result_isa.csv"))

command = "/Users/pro/.cargo/bin/cargo run --package cyclegg --bin cyclegg --release -- examples/clam_no_lemmas.ceg -d 100000 -t %d -r --only-generalize > %s" % (time_limit, os.path.join("results", output_dir, "output-clam"))
os.system(command)
os.system("cp target/results.csv %s" % os.path.join("results", output_dir, "result_clam.csv"))