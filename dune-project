(lang dune 2.8)
(name coq-hyperocm)
(version 0.1.0)
(using coq 0.2)

(generate_opam_files true)

(license MIT)
(authors "inQWIRE")
(maintainers "inQWIRE Developers")
; (source (github inQWIRE/VyZX))

(package
 (name coq-hyperocm)
 (synopsis "")
 (description ""
 )

 (depends
   (coq-quantumlib (>= 1.7.0))
   (coq (>= 8.20))
   (yojson (>= 0))))
