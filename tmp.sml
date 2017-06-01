open arithmeticTheory listTheory;


set_fixity "divides" (Infix(NONASSOC, 450));

val divides_def = 
 Define 
  `a divides b = ?x. a = b * x`;

val prime_def = 
 Define
  `prime p = p <> 1 /\ !x. x divides p ==> (x = 1) \/ (x = p)`

val PRIME_FACTOR = store_thm
("PRIME_FACTOR",
``!n. ~(n = 1) ==> ?p. prime p /\ p divides n``,
completeInduct_on `n` 
>> 
