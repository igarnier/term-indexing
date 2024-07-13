
bench:
	dune exec ./bench/bench.exe --profile=release

coverage:
	dune runtest --instrument-with bisect_ppx --force
	bisect-ppx-report html
