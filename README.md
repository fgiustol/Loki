# Loki
This is a prototype implementation of Loki, a strong-verifiable coercion-resistant voting system based on the paper "Thwarting Last-Minute Voter Coercion" by Rosario Giustolisi, Maryam Sheikhi, and Carsten Schuermann, accepted to IEEE S&P 2024.

Loki requires [zksk](https://github.com/spring-epfl/zksk) for the implementation of disjunctive zero-knowledge proofs. Make sure that it is installed correctly by following the [zksk instructions](https://github.com/spring-epfl/zksk#getting-started).

It also requires the attrs python packages, which can be obtained by pip
```
pip install attrs
```

## Debian
Loki has been tested on Debian 10. Package dependencies for zksk can be obtained via 
```
apt-get install libffi-dev libssl-dev
```

## MacOS

Loki has been tested on MacOS Sonoma 14.1 with Homebrew Python3. Known issues with the installation of zksk and its dependencies could be addressed by installing openssl version 1.1
```
brew install openssl@1.1
```


and setting path and environment variables according to the output of ``` brew info openssl@1.1 ```. For example:
```
export LDFLAGS="-L/opt/homebrew/opt/openssl@1.1/lib"
export CPPFLAGS="-I/opt/homebrew/opt/openssl@1.1/include"
export PKG_CONFIG_PATH="/opt/homebrew/opt/openssl@1.1/lib/pkgconfig"

```

## Acknowledgments
An initial version of the implementation of the proofs for ballot verifiability is available as part of a [BSc Project](https://github.com/Myssenberg/BScProject).

## Contacts
Rosario Giustolisi <rosg@itu.dk>
