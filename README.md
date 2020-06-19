# Kex

Kex is a white-box fuzzer tool for Java bytecode.

# Dependencies

* [z3-java](https://aur.archlinux.org/packages/z3-java/) v4.8.6

  you need to manually install jar package with java bindings to your local maven repository using
  following command:
  ```
  mvn install:install-file -Dfile=/usr/lib/com.microsoft.z3.jar -DgroupId=com.microsoft 
  -DartifactId=z3 -Dversion=4.8.6 -Dpackaging=jar
  ```
* [boolector-java](https://aur.archlinux.org/packages/boolector-java/) v3.2.1

# Build

* build jar with all the dependencies:
    ```
    mvn clean package
    ```

* build with only one SMT solver support:
    ```
    mvn clean package -Psolver
    ```
    where `solver` stand for required solver name (`boolector` or `z3`) 

Run all the tests:
```
mvn clean verify
```

# Kotlin refinement types inference

Run inference for jar file with 

`python refinements.py --jar <path to jar file>`

Results are stored as a log file in a results directory at the same path as analyzed jar file.

# Usage

```
Usage: kex
    --config <arg>                  configuration file
 -h,--help                          print this help and quit
 -j,--jar <arg>                     input jar file path
    --log <arg>                     log file name (`kex.log` by default)
 -m,--mode <arg>                    run mode: bmc, concolic or debug
    --option <section:name:value>   set kex option through command line
    --output <arg>                  target directory for instrumented bytecode
                                    output
    --ps <arg>                      file with predicate state to debug; used
                                    only in debug mode
 -t,--target <arg>                  target to analyze: package, class or method
```
