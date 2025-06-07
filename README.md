# A Construction of the Urysohn Universal Space in Lean4 

This repository contains a construction of the Urysohn Universal Space in [Lean4](https://lean-lang.org/). To run this code for yourself, there are several options: 
- Depending on how far you are into the future, the quickest and simplest way might be to copy-paste the contents of  ``UrysohnFormal/UrysohnSpace.lean`` at [live.lean-lang.org](https://live.lean-lang.org) and explore it in the web editor. This is liable to stop working eventually as Lean evolves. (Last tried succesfully on 01/05/2025)
- To run this locally [you will need to install lean on your machine first](https://leanprover-community.github.io/get_started.html), and then you can follow [the offical instructions for working on an existing project](https://leanprover-community.github.io/install/project.html#working-on-an-existing-project). The last Lean version this was run succesfully in was v4.19.0-rc3. In VSCode, you can select the Lean version by clicking ∀ symbol in the top right then doing ``> Project Actions > Select project lean version``.
- You can follow option 2) but work entirely online on GitHub Codespaces: \
   [![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/luigi-massacci/UrysohnFormal)

Note that the project contains one big computation that can take longer than the default timeout (a simple if time consuming improvement would be to cut it up into smaller pieces). If you get an error `(deterministic) timeout ...`, find the line `set_option maxHeartbeats` and increase the number (ex. double it) and it should eventually compile). 

Feel free to email me at "name" "dot" "surname" "at" institution "dot" countryabbr if you would like to pick up this project or have any questions.  
