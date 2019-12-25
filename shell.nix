let

  nixpkgs-source = builtins.fetchTarball {
    url =
      "https://github.com/NixOS/nixpkgs-channels/archive/a06925d8c608d7ba1d4297dc996c187c37c6b7e9.tar.gz";
    sha256 = "0xy6rimd300j5bdqmzizs6l71x1n06pfimbim1952fyjk8a3q4pr";
  };

  pkgs = import nixpkgs-source { };

  # The darwin agda standard library is listed as broken but this is not
  # actually true. Hence we import just the standard library from the broken
  # package set.
  AgdaStdlib =
    (import nixpkgs-source { config = { allowBroken = true; }; }).AgdaStdlib;

  standard-library-agda-lib = pkgs.writeText "standard-library.agda-lib" ''
    name: standard-library
    include: ${AgdaStdlib}/share/agda
  '';

  agdaDir = pkgs.stdenv.mkDerivation {
    name = "agdaDir";

    phases = [ "installPhase" ];

    installPhase = ''
      mkdir $out
      echo "${standard-library-agda-lib}" > $out/libraries
      echo "standard-library" > $out/defaults
    '';
  };

in pkgs.mkShell {
  name = "agda-shell-with-stdlib";
  builtInputs = [ pkgs.haskellPackages.Agda pkgs.emacs ];
  AGDA_DIR = agdaDir;
}

