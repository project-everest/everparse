Minimal viable c3d:
- merge Guido's PR: https://github.com/project-everest/everparse/pull/35/files
- review and iterate on syntax and resulting output (see documentation in PR above)
- understand build and iron out kinks (mysteries in linking on different platforms suggests there might be deeper build issues at play here)
- use the resulting standalone clang-c3d.exe to adopt c3d syntax in the Windows tree for a simple use-case (RNDIS) and declare minimum viable product

Paying off technical debt (all documented in great detail at: https://github.com/project-everest/everparse/blob/c3d/c3d/Notes):
- improve c3d implementation to limit internal duplication as it is likely to cause maintenance difficulties going forward -- lots of repetition in classes declaration and methods
- iterate and finish patch #1: https://reviews.llvm.org/D86169 -- this will cut our reliance on a custom patch for clang and will make build & distribution much easier -- after this we won't need a custom clang anymore!
- patch #2: (also described in LLVM review above): allow plugins to extend the ParsedAttr hierarchy, possibly via an OpaquePtr for custom parsed objects -- see inline comment of mine at https://github.com/project-everest/everparse/blob/c3d/c3d/src/C3d.cpp#L755 -- this will greatly simplify our implementation
- patch #3: (also described in LLVM review above): allow plugins to extend the Attr hierarchy possibly using tablegen so as to not be constrained by a string representation -- also will greatly simplify our implementation
- get a review of our plugin from a clang frontend expert who can suggest improvements and idiomatic ways of doing things (code is very verbose in places)

Make the tool usable (the long tail)
- proper error reporting with decent suggestions (see e.g. https://github.com/project-everest/everparse/blob/c3d/c3d/src/C3d.cpp#L439)
- proper commenting out of the attributes when spewing out a "cleaned up" file (see e.g. https://github.com/project-everest/everparse/blob/c3d/c3d/src/C3d.cpp#L1449) -- this can perhaps be done using the cursor API but I'm not sure
- make it work with 3d's upcoming multi-file mode (should be fine)
- make sure that c3d performs enough analyses (scoping, names, etc.) to guarantee that any file c3d accepts will be recognized as valid 3d later on
- work on a larger example and fix the myriad of little inconveniences that are currently marked as TODOs in the source
- make sure the tool can process windows headers without flinching -- I have a proof-of-concept way to do this in the tree but it needs to be confirmed on larger examples
