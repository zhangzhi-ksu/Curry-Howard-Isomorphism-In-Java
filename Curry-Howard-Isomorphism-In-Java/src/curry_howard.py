
'''
   #################################################
'''

''' and-introduction rule "^i":

	<pre>
 	 P   Q
	-------- (^i)
	 P ^ Q
	</pre>

    ... can be thought of as a program step or a method that takes a value of
    type P and Q and produces a value of type (P, Q).
     
    By Curry-Howard isomorphism, if P and Q are propositions, then it can be 
    interpreted as taking evidence of the truth of propositions P and Q 
    respectively and producing evidence of the truth of proposition P ^ Q.
'''
def and_i(p, q):
	return (p, q)

''' And-elimination rule "^e1"

	<pre>
	 P ^ Q
	------- (^e1)
	   P
	</pre>

    ... can be thought of as a program step or method that takes an value of
    type (P, Q) returns a value of type P.
     
    By Curry-Howard isomorphism, if P and Q are propositions, then it can
    be interpreted as taking evidence of the truth of proposition P ^ Q
    and producing a evidence of the truth of P.
'''
def and_e1(pq):
	return pq[0]

''' And-elimination rule "^e2"

	<pre>
	 P ^ Q
	------- (^e2)
	   Q
	</pre>	

    ... can be thought of as a program step or method that takes an value of
    type (P, Q) returns a value of type Q.
     
    By Curry-Howard isomorphism, if P and Q are propositions, then it can
    be interpreted as taking evidence of the truth of proposition P ^ Q	
    and producing evidence of the truth of Q.
'''
def and_e2(pq):
	return pq[1]

'''
   #################################################
'''

'''
   	For any types P and Q, we want instances of either P or Q to provide
   	evidence of the proposition P v Q.
    
   	To achieve this, note that if P v Q is true, our evidence needs to
   	indicate *which* of P or Q is true. 
    
    
   	There are a number of ways to achieve this. Here we do it with a pair
   	(a special case of tuple type in Python), with its second item carrying
   	the evidence of either P or Q, and its first item being a tag indicating 
   	*which* kind of evidence in the second item. If the first item is 'left',
   	it means an evidence of P being true in its second item, and if the first 
   	item is 'right', it means an evidence of Q being true in its second item.
   	- ('left' , evidence_of_P_is_true)
   	- ('right', evidence_of_Q_is_true)

  	Below is some other technical stuff for people interested in functional
    programming. [You don't need to understand the rest of the comment.]
   
   	Or P Q, written P + Q, is the disjoint type sum of P and Q, which is
   	defined in OCaml as:
 
   	<pre>
   	   Inductive Or (P Q:Type) : Type :=
   	     | left  : P -> Or P Q  
   	     | right : Q -> Or P Q.
   	</pre>

   	where 'left' and 'right' are type constructors, which are used to make 
   	both P and Q as subtype of (Or P Q) and (Or P Q) = P + Q
	   
   	Or P Q = left P + right Q
'''

''' Or-introduction rule "vi1"

	<pre>
 	   P 
	-------- (vi1)
	 P v Q
	</pre>

    ... can be thought of as a program step or a method that takes a value of
    type P and produces a value of type P v Q.
    
    In the implementation of the method, we use a pair to associate the value 
    of P with a tag 'left', which has the effect of "tagging" the object so  
    that we know the "left side" of P v Q is true.
     
    By Curry-Howard isomorphism, if P and Q are propositions, then it can be 
    interpreted as taking evidence of the truth of proposition P and producing 
    evidence of the truth of proposition P v Q.
'''
def or_i1(p):
	return ("left", p)

''' Or-introduction rule "vi2"

	<pre>
 	   Q 
	-------- (vi2)
	 P v Q
	</pre>

    ... can be thought of as a program step or a method that takes a value of
    type Q and produces a value of type P v Q.
    
    In the implementation of the method, we use a pair to associate the value 
    of Q with a tag 'right', which has the effect of "tagging" the object so  
    that we know the "right side" of P v Q is true.
     
    By Curry-Howard isomorphism, if P and Q are propositions, then it can be 
    interpreted as taking evidence of the truth of proposition Q and producing 
    evidence of the truth of proposition P v Q.
'''
def or_i2(q):
	return ("right", q)

''' Or-elimination rule "ve"

	<pre>
               ...P assume   ...Q assume
       P v Q   ...R          ...R
    --------------------------------------- (ve)
                       R
    </pre>

	... can be though of as a program step or a method 'or_e' that takes
    three inputs...
    
     (1) a value of P v Q
    
     (2) a deduction method that transforms values of P into values of R
     
     (3) a deduction method that transforms values of Q into values of R
     
    ...and produces a value of type R.
    
    'or_e' works by checking the tag ('left' or 'right') to see whether 
    'pORq' is a value of P or Q, and then extract the corresponding value.
     
    If it's a value of P, which is indicated by tag 'left', then the 
    deduction method 'pDEDUCEr' is applied to return an object of type R.
     
    If it's a value of Q, which is indicated by tag 'right', then the 
    deduction method 'qDEDUCEr' is applied to return an object of type R.


    By Curry-Howard isomorphism, if P and Q are propositions, then it can 
    be interpreted as taking evidence of the truth of proposition P v Q 
    and two deductions (...P assume ...R) and (...Q assume ...R).

    First, it checks the tag ('left' or 'right') to see whether 'pORq' is an 
    evidence of P or Q.
     
    If it's an evidence of P, which is tagged by 'left', then the subproof that 
    proves R given P is activated to return an evidence of R.
     
    If it's an evidence of Q, which is tagged by 'right', then the subproof 
    that proves R given Q is activated to return an evidence of R.
'''
def or_e(pORq, pDEDUCEr, qDEDUCEr):
  r = None
	if pORq[0] == "left":
		r = pDEDUCEr(pORq[1])
	else:
		r = qDEDUCEr(pORq[1])
	
  return r

'''
   #################################################
'''

'''
	Several of our proof rules use sub-proofs that look like this...
   	
   	<pre>
   	      ... P  assumption
   	      ...
   	      ... Q
   	</pre>
   
   	We can think of such a sub-proof as a method that, if given evidence for
   	P, it can produce evidence for Q.
'''

''' Imply-introduction rule "->i"

    <pre>
	 ... P assume
     ... Q
    -------------- (->i)
        P -> Q
    </pre>

   	... can be thought of as a program step or a method that takes as input
    a deduction (i.e., a method) that provides a way to transform a value of 
    type P into a value of type Q and produces a method of type P -> Q.
     
    By Curry-Howard isomorphism, it can be interpreted as taking a subproof 
    that, given evidence of the truth of propositions P can produce evidence 
    of the truth of proposition Q.
    
    In our representation, a subproof (the stuff above the bar in the ->i
    rule) is represented as a deduction method.
     
    The deduction method takes as input evidence for the truth of P and 
    produces evidence of the truth of Q. Thus, evidence for the truth of the 
    proposition P -> Q is a method (aka procedure, subroutine) for transforming 
    P evidence into Q evidence.
'''
def imply_i(pDEDUCEq):
	''' 'pDEDUCEq' represent a method that takes a value of type P and produces 
		a value of Q. 
    '''
	def pIMPLYq(p):
		q = pDEDUCEq(p)
		return q

	return pIMPLYq


''' Imply-elimination rule "->e"

	<pre>
	 P -> Q
     P
    -------- (->e)
        Q
    </pre>

    ... can be thought of as a program step or method that takes a method of
    type P -> Q and a value of type P and returns a value of type Q.
    
    By Curry-Howard isomorphism, if P and Q are propositions, then it can
    be interpreted as taking evidence of the truth of proposition P -> Q, 
    evidence of the truth of P, and producing an evidence of the truth of Q.
    
    Intuitively, the evidence for Q is constructed by using the evidence for
    P -> Q. Specificly, the evidence for P -> Q is a deduction method that 
    transforms P evidence into Q evidence. Because we have evidence for P 
    (the argument p of the method), we can apply the P -> Q evidence (i.e., 
   	the pIMPLYq method) to the P evidence to get the Q evidence.
'''
def imply_e(pIMPLYq, p):
	q = pIMPLYq(p)
	return q

'''
   #################################################

    S u m m a r y

   	For any propositional variable P, Q, R, whenever the propositional variable
    is true, we assume that there is some way of representing evidence of the
    truth of the propositional variable.
    
    For any non-primitive proposition built with the connectives ^, v, and ->,
    we can represent evidence of the truth of that proposition using Python 
    pairs/tuples and functions.
    
    Evidence for P ^ Q is a pair/tuple with two items: one holding evidence of
    P and the other holding evidence of Q.
   
    Evidence for P v Q is a pair/tuple with its first item being a tag 
    indicating that which of P or Q is true. In our case, the "tag" is 
    represented by either a string 'left' or 'right'. If the tag indicates 
    that P is true, then the evidence object for P v Q includes evidence of P. 
    If Q is true, then the evidence object for P v Q includes evidence of Q.
   
    Evidence for P -> Q is a method that can transform evidence of P into 
    evidence of Q.
'''

''' ----------- Proofs -------------
   	p ^ q  |-  q ^ p
    
   	1. p ^ q                 premise
   	2. p                      ^e1 1
   	3. q                      ^e2 1
   	4. q ^ p                  ^i 3,2
'''
def and_example(pANDq):
	                    # line 1 premise: P ^ Q (pANDq) 
	p = and_e1(pANDq)   # line 2 ^e1 applied to P ^ Q
	q = and_e2(pANDq)   # line 3 ^e2 applied to P ^ Q
	qANDp = and_i(q, p) # line 4 ^i  applied to Q and P
	return qANDp

''' ----------- Proofs -------------
    q  |-  p v q v r

   	1. q                    premise
   	2. p v q                  vi2 1
   	3. p v q v r              vi1 2
'''
def or_example(q):
	                      # line 1 premise: Q (q)
	pORq = or_i2(q)       # line 2 vi2 applied to Q
	pORqORr = or_i1(pORq) # line 3 vi1 applied to P v Q
	return pORqORr


''' ----------- Proofs -------------
	(p ^ q) -> r,  p --> q,  p  |-  r

	1. (p ^ q) -> r           premise
	2. p                      premise
	3. p -> q                 premise
	4. q                      ->e 3,2
	5. p ^ q                  ^i 2,4
	6. r                      ->e 1,5
'''
def example1(pqIMPLYr, pIMPLYq, p):
	                             # line 1 premise: (P ^ Q) -> R (pqIMPLYr)
	                             # line 3 premise: P -> Q (pIMPLYq)
	                             # line 2 premise: P (p)
	q = imply_e(pIMPLYq, p)      # line 4 ->e applied to P -> Q and P      
	pANDq = and_i(p, q)          # line 5 ^i  applied to P and Q
	r = imply_e(pqIMPLYr, pANDq) # line 6 ->e applied to (P ^ Q) -> R and P ^ Q
	return r

''' ----------- Proofs -------------
	(p v q) -> r,  q |-  r

	1. (p v q) -> r        premise
	2. q                   premise
	3. p v q               vi2 2
	4. r                   ->e 1,3
'''
def example2(pqIMPLYr, q):
	                            # line 1 premise: (P V Q) -> R (pqIMPLYr)
	                            # line 2 premise: Q (q)
	pORq = or_i2(q)             # line 3 vi2 applied to Q
	r = imply_e(pqIMPLYr, pORq) # line 4 ->e applied to (P v Q) -> R and P v Q
	return r

''' ----------- Proofs -------------
	p,  (q ^ p) -> r  |-  q -> r 

	1. p                     premise
	2. (q ^ p) -> r          premise
		... 3. q                  assumption
		... 4. q ^ p              ^i 3,1
		... 5. r                  ->e 2,4
	6. q -> r                 ->i 3-5
'''
def example3(p, qpIMPLYr):
	                                 # line 1 premise: P (p)
	                                 # line 2 premise: (Q ^ P) -> R (qpIMPLYr)
	def qDEDUCEr(q):
		                             # line 3 assumption: Q (q)
		qANDp = and_i(q, p)          # line 4 ^i  applied to Q and P
		r = imply_e(qpIMPLYr, qANDp) # line 5 ->e applied to (Q ^ P) -> R and Q ^ P
		return r 

	qIMPLYr = imply_i(qDEDUCEr) # line 6 ->i applied to deduction (... Q assume ... R)
	return qIMPLYr


''' ----------- Proofs -------------
	p --> r,  q --> r  |-  (p v q) --> r

	1. p --> r            premise
	2. q --> r            premise
		... 3. p v q               assumption

		... ... 4. p                       assumption
		... ... 5. r                       -->e 1,4

		... ... 6. q                       assumption
		... ... 7. r                       -->e 2,6

		... 8. r                    ve 3,4-5,6-7
	9. (p v q) --> r     -->i 3-8
'''
def example4(pIMPLYr, qIMPLYr):
                                    # line 1 premise: P -> R (pIMPLYr)
                                    # line 2 premise: Q -> R (qIMPLYr)
	def pqDEDUCEr(pORq):
		                            # line 3 assumption: P v Q (pORq)
		def pDEDUCEr(p):
			                        # line 4 assumption: P (p)
			r = imply_e(pIMPLYr, p) # line 5 ->e applied to P -> R and P
			return r
		def qDEDUCEr(q):
			                        # line 6 assumption: Q (q)
			r = imply_e(qIMPLYr, q) # line 7 ->e applied to Q -> R and Q
			return r
		r = or_e(pORq, pDEDUCEr, qDEDUCEr) # line 8 ve applied to P v Q, and deductions (... P assume ... R) and (... Q assume ... R) 
		return r

	pqIMPLYr = imply_i(pqDEDUCEr)               # line 9 ->i applied to deduction (... P V Q assume ... R)
	return pqIMPLYr

''' ----------- Proofs -------------
	q |- p -> (q ^ p)

	1. q               premise
		... 2. p           assumption      ...apply the ->i tactic
		... 3. q ^ p       ^i 1,2
	4. p -> (q ^ p)    ->i 2-3
'''
def example5(q):
	                              # line 1 premise Q (q)
	def pDEDUCEqp(p):
			                      # line 2 assumption: P (p)
		qANDp = and_i(q, p)       # line 3 ^i  applied to Q and P
		return qANDp

	pIMPLYqp = imply_i(pDEDUCEqp) # line 4 ->i applied to deduction (... P assume ... Q ^ P)
	return pIMPLYqp


''' ----------- Proofs -------------
	p -> (q -> r) |- (p -> q) -> (p -> r)

	1. p -> (q -> r)     premise
	... 2. (p -> q)      assumption    ...apply the ->i tactic
    	... 3. p         assumption
    	... 4. q -> r    ->e 1,3
    	... 5. q         ->e 2,3
    	... 6. r         ->e 4,5
	... 7. p -> r        ->i 3-6
	8. (p -> q) -> (p -> r)
'''
def example6(pIMPLYqir):
	                                        # line 1 premise: P -> (Q -> R) (pIMPLYqir)
	def piqDEDUCEpir(pIMPLYq):
		                                    # line 2 assumption: P -> Q (pIMPLYq) 
		def pDEDUCEr(p):
			                                # line 3 assumption: P (p)
			qIMPLYr = imply_e(pIMPLYqir, p) # line 4 ->e applied to P -> (Q -> R) and P
			q = imply_e(pIMPLYq, p)         # line 5 ->e applied to P -> Q and P
			r = imply_e(qIMPLYr, q)         # line 6 ->e applied to Q -> R and Q
			return r

		pIMPLYr = imply_i(pDEDUCEr)         # line 7 ->i applied to deduction (... P assume ... R)
		return pIMPLYr

	piqIMPLYpir = imply_i(piqDEDUCEpir)     # line 8 ->i applied to deduction (... P-> Q assume .... P -> R)
	return piqIMPLYpir



'''
   #################################################

                         Tests

   #################################################
'''
import unittest
class TestFunctions(unittest.TestCase):
    def setUp(self):
        # p, q and r can be initialized to objects of other types
        self.p = 'p'
        self.q = 'q'
        self.r = 'r'

    def test_and_example(self):
        print("(1) p ^ q  |-  q ^ p")
        pANDq = and_i(self.p, self.q)
        and_example(pANDq)

    def test_or_example(self):
        print("(2) q  |-  p v q v r")
        or_example(self.q)

    def test_example1(self):
        print("(3) (p ^ q) -> r,  p --> q,  p  |-  r")
        def pqDEDUCEr(pANDq):
            return self.r
        def pDEDUCEq(p):
            return self.q
        pqIMPLYr = imply_i(pqDEDUCEr)
        pIMPLYq  = imply_i(pDEDUCEq)
        example1(pqIMPLYr, pIMPLYq, self.p)

    def test_example2(self):
        print("(4) (p v q) -> r,  q |-  r")
        def pqDEDUCEr(pORq):
            return self.r
        pqIMPLYr = imply_i(pqDEDUCEr)
        example2(pqIMPLYr, self.q)

    def test_example3(self):
        print("(5) p,  (q ^ p) -> r  |-  q -> r")
        def qpDEDUCEr(qANDp):
            return self.r
        qpIMPLYr = imply_i(qpDEDUCEr)
        example3(self.p, qpIMPLYr)

    def test_example4(self):
        print("(6) p --> r,  q --> r  |-  (p v q) --> r")
        def pDEDUCEr(p):
            return self.r
        def qDEDUCEr(q):
            return self.r
        pIMPLYr = imply_i(pDEDUCEr)
        qIMPLYr = imply_i(qDEDUCEr)
        example4(pIMPLYr, qIMPLYr)

    def test_example5(self):
        print("(7) q |- p -> (q ^ p)")
        example5(self.q)

    def test_example6(self):
        print("(8) p -> (q -> r) |- (p -> q) -> (p -> r)")
        def pDEDUCEqir(p):
            def qDEDUCEr(q):
                return self.r
            qIMPLYr = imply_i(qDEDUCEr)
            return qIMPLYr
        pIMPLYqir = imply_i(pDEDUCEqir)
        example6(pIMPLYqir)

if __name__ == '__main__':
  unittest.main()






