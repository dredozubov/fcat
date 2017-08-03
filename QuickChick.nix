{stdenv, fetchgit, coq, coqPackages}:

let revision = "4fb47fdb2432d9be46fee5cba5e0e6a655f04c45"; in

stdenv.mkDerivation rec {

  name = "coq-QuickChick-${coq.coq-version}-${version}";
  version = "20170710-${builtins.substring 0 7 revision}";

  src = fetchgit {
    url = git://github.com/QuickChick/QuickChick.git;
    rev = revision;
    sha256 = "09a5lxk88sq4csbpr145r1q3js5g2801c6ljqww6s5ddimhdpk7y";
  };

  buildInputs = [ coq.ocaml coq.camlp5 ];
  propagatedBuildInputs = [ coq coqPackages.ssreflect ];

  enableParallelBuilding = true;

  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

  meta = with stdenv.lib; {
    homepage = git://github.com/QuickChick/QuickChick.git;
    description = "Randomized property-based testing plugin for Coq; a clone of Haskell QuickCheck";
    maintainers = with maintainers; [ dredozubov ];
    platforms = coq.meta.platforms;
  };

}
