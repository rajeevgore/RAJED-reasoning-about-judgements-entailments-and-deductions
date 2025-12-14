<h1>Verified tableaux for K, KT, S4</h1>
This directory contains the Coq/Rocq files on the formal verification of tableau procedures for K, KT, S4 associated with the paper "Verified Tableaux: from Modal Logics to Modal Fixpoint Logics" by Rajeev Goré and Anthony Peigné.
The files formalising tableaux for LTL can be found <a href=https://github.com/rajeevgore/RAJED-reasoning-about-judgements-entailments-and-deductions/tree/main/Verified-tableaux-for-LTL>here</a>.

<h2>Building instructions</h2>
The project requires Coq version 8.17.1 and may not compile on other versions. To obtain that version with <a href=https://opam.ocaml.org/doc/Install.html>opam</a>, simply run <code>opam pin coq 8.17.1</code>.
Then it suffices to run <code>make</code> at the root directory to compile all the files. This will also extract an OCaml tableau decision procedures for K, KT, S4.
