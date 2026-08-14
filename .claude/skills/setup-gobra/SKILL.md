---
name: setup-gobra
description: Setup Gobra in a pre-existing Git repository
---

# Setup gobra to verify a package

## Quick start

1. Set-up Gobra for the current package: If you are in a Git repository, first you may want to add the gobra-action (https://github.com/viperproject/gobra-action) Github Action to your CI. If it does not exist already, set a CI workflow that checks-out your repository and runs gobra-action on it. Add the package you want to verify as a separate step in that workflow. Check the README.md of the gobra-action for instructions. Make the default timeout 3 min.

2. Check if the root of the module of the package under verification already has a `gobra` folder. If not, create it -- it will be used for storing specifications and stubs for unverified libraries you depend on, as well as verified utility packages containing ghost code. Check if the root of the module of the package under verification already has a `gobra-mod.json` file containing the project-level configuration of the project. If not, create it. The following is a good initial json config:
```json
{
  "assert_timeout" 3000,
  "includes": [".", "gobra/"],
  "module" : ???,
  "only_files_with_header": true,
  "other": ["--experimentalFriendClauses"],
  "require_triggers": true,
}
```
This config sets up the following behaviour:
- `assert_timout`: guarantees that most (though not all) long SMT queries are killed within 3 seconds.
- `includes`: locations against which imports are resolved. Analogous to the -I flag in C compilers.
- `module` : the name of the module. Replace `???` by the actual module name and path.
- `only_files_with_header` : verify the files that were explicitely selected to verify by adding a `// +gobra` header to them. Ignores all .go files without this annotations.
- `other` : passes flags directly to Gobra. In this config, it is just enabling an experimental, but useful, feature.


3. If it does not exist, create a `gobra.json` at the root of the package under verification. This will contain the package specific configurations. By default, an empty config is OK.
```json
{}
```

4. Add a `spec.gobra` file to the current package that should follow the template below:
```gobra

// Enables Gobra in the current file
// +gobra

package ... // should be replaced with
```
If you are in a setting where you have a precompiled gobra.jar, you can make sure verification works by running the jar against the package:
```sh
java -jar PATH/TO/gobra.jar --config PATH/TO/PKG
```
If Gobra returns with 0 errors, then all is set-up for the package and it is time to start verifying.