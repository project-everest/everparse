This project **cannot** be edited with Visual Studio, because module
dependencies straddle folder boundaries, thus violating a Visual
Studio requirement that all files of a given subfolder be listed
contiguously (see https://stackoverflow.com/questions/2908473/f-compiler-order-of-source-files and https://stackoverflow.com/questions/22845020/visual-studio-f-project-cant-have-two-folders-in-a-file-tree-with-the-same-na )
