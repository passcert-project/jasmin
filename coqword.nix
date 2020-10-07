{ stdenv, fetchFromGitHub, coqPackages }:

let inherit (coqPackages) coq; in

let mathcomp = coqPackages.mathcomp-algebra_1_11 or (coqPackages.mathcomp_ "1.11.0").algebra; in

let rev = "7c650450e03310ca67bdccb64c95be82116945c7"; in

stdenv.mkDerivation rec {
  version = "0.0-git-${builtins.substring 0 8 rev}";
  name = "coq${coq.coq-version}-coqword-${version}";

  src = fetchFromGitHub {
    owner = "jasmin-lang";
    repo = "coqword";
    inherit rev;
    sha256 = "1b4p67599s6cqbs3r1pd736dq5zivvi3w8wbl4dhcg6mnzbgvkyg";
  };

  buildInputs = [ coq ];

  propagatedBuildInputs = [ mathcomp ];

  installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];

  meta = {
    description = "Yet Another Coq Library on Machine Words";
    license = stdenv.lib.licenses.cecill-b;
    inherit (src.meta) homepage;
    inherit (coq.meta) platforms;
  };
}
