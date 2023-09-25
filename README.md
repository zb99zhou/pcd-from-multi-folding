## Proof-carrying data from multi-folding schemes

TODO: A complete implementation of a proof-carrying data scheme from multi-folding schemes.

This implementation is not meant to be used in production. 

<!--
<center>
<img
    width="65%"
    src="https://github.com/privacy-scaling-explorations/multifolding-poc/raw/main/doc/images/multifolding_diagram.png"
/>
</center>
-->


## References

The following paper provides details and proof of security of this implementation:  

[Proof-Carrying Data from Multi-folding Schemes](https://eprint.iacr.org/2023/1282)  
Zibo Zhou, Zongyang Zhang, Jin Dong, and Zhiyu Zhang  
IACR ePrint 2023/1282

For efficiency, our implementation is instantiated over a cycle of elliptic curves. The structure refers to the following paper:  

[Revisiting the Nova Proof System on a Cycle of Curves](https://eprint.iacr.org/2023/969)  
Wilson Nguyen, Dan Boneh, and Srinath Setty  
IACR ePrint 2023/969
