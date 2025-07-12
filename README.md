# Overview 
Just a tool to simplify relation normalization process, evaluate database design. 

![menu](./assets/interactive_menu_02.png)
![decompose 3nf](./assets/3nf_02.png)
![decompose bcnf](./assets/bcnf_02.png)

And more!


# Usage 
```bash 
python3 main.py 
```


# Todos
- [x] Attribute closure 
- [x] Armstrong: ir2, ir3, ir4, ir5
- [x] Check two Functional Dependency (FD) set is equivalent
- [x] Find closure Functional Dependency set (FDs) from Armstrong rule set
- [x] Minimal cover of FDs
- [x] Find key from FDs
- [x] Check collection of attribute is super key of relation 
- [x] Decompose relation to 3NF from FDs
- [x] Decompose relation to BCNF from FDs
- [x] Menu interactive
- [ ] Check current Normal Form of relation (in general normal form definition)
- [ ] Test Nonadditive Join Property after decomposition relation
- [ ] Args parser integrate click
- [ ] Reduce random order of set iterator in minimal_cover method

# Disclaimers
All code is kept in one file for portability and ease of execution.

User input binding with dynamic injection, same idea how Spring implement IoC 🤞. I love Spring btw. 

Follow TDD but in a suck way 💀. 
