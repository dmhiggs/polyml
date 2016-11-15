
(*in_list - 10%*)

(*This function should return true if the first argument is a member 
of the second argument and have type (''a * ''a list) -> bool.*)

fun in_list (x, []) = false
 	| in_list (x, (y::ys)) =
 		if x = y
 		then true
 		else in_list (x, ys);



(*intersection - 10%

This function should return the intersection of two lists, 
and have type ''a list * ''a list -> ''a list. . 
Maybe you can make use of in_list?*)

fun intersection ([],[]) = []
 	| intersection ([], (y::ys)) = []
 	| intersection ((x::xs), []) = []
 	| intersection ((x::xs), (y::ys)) =
		if ((intersection ((x::[]),xs)) <> [])
		      then intersection (xs, (y::ys))
		else 
		      if (x <> y)
		      then (intersection ((x::[]),ys))@(intersection (xs, (y::ys)))
		      else x::(intersection (xs, (y::ys)))	 	
		     ;



(*union - 10%

This function should return the union of two lists. 
Each value should appear in the output list only once but the order does not matter. 
In the intersection function above the two lists were supplied as a tuple. 
That is, it had type (''a list * ''a list) -> ''a list. 
Make union a function of two arguments: it should have type ''a list -> ''a list -> ''a list.*)

(* this looks like funions *)
fun union [] [] = []
 	| union [] (y::ys) =  union (y::[]) ys
	| union (x::xs) [] = union (x::[]) xs
 	| union (x::xs) (y::ys) = 
		intersection (
			((x::xs)@(y::ys)),((x::xs)@(y::ys))
			);



(*filter and reverse - 10%

filter takes as its first argument a one-argument function, 
called a predicate, which returns true or false, 
and as its second argument a list. 
It returns a list of all elements in the second argument that 
satisfy that predicate. 
The elements must appear in the result in the same order 
that they appear in the original list.
tail recursive*)

fun filter pred [] = []
	| filter pred (x::xs) = let
		fun add pred [] l = l
		  | add pred (x::xs) l = 
			if pred x
			then add pred xs (l@[x])
			else add pred xs l
		in
		   (add pred (x::xs) [])
		end;



(*groupNl and groupNr - 10%

These functions take two arguments. 
The first is an integer and the second is a list. 
The idea is to produce a result in which the elements of 
the original list have been collected into sublists 
each containing N elements (where N is the integer argument). 
Thus the type of each of these is int -> 'a list -> 'a list list. 
The difference between the two functions is how they handle 
the left-over elements of the list when the integer doesn't 
divide the length of the list evenly. 
groupNl treats the initial elements of the list as the extras, 
thus the result starts with a list of between 1 and N elements 
and all the remaining elements of the result list contain N elements. 
groupNr does the opposite: the final group contains between 1 and 
N elements and all the rest contain N elements.*)

fun groupNl x [] = [] : int list list
  | groupNl x (y::ys) = 
	if (x <= 0)
	then []
	else let
		val z = 0
		fun add x w [] [] [] = []
		  | add x w [] [] l2 = l2
		  | add x w [] l l2 = [l]@l2
		  | add x w (y::ys) l l2 = let
			fun last [] = []
			  | last [r] = [r]
			  | last (_::rs) = last rs
			in
				if w > z
				then if (ys <> [])
				     then let
					fun droplast [] [] = []
					  | droplast [] l2 = l2
					  | droplast (y::ys) l2 = 
						if (ys = [])
						then droplast [] l2
						else droplast ys (l2@[y])
					in
					   add x (w-1) (droplast (y::ys) []) ((last ys)@l) l2
					end
				     else add x (w-1) ys (y::l) l2
				else add x x (y::ys) [] ([l]@l2)
			end
	     in
		add x x (y::ys) [] []
	     end;

fun groupNr x [] = [] : int list list
  | groupNr x (y::ys) = 
	if (x <= 0)
	then []
	else let
		val z = 0
		fun add x w [] [] [] = []
		  | add x w [] [] l2 = l2
		  | add x w [] l l2 = l2@[l]
		  | add x w (y::ys) l l2 = 
			if w > z
			then add x (w-1) ys (l@[y]) l2
			else add x x (y::ys) [] (l2@[l])
	     in
		add x x (y::ys) [] []
	     end;



(*mergesort - 15%

This function takes two arguments. 
The first argument is a function called a comparator and 
takes as its argument a pair (two-tuple) and returns a boolean. 
The second argument is a list. The type of the sorting function is 
('a * 'a -> bool) -> 'a list -> 'a list. 
The function mergesort returns a list consisting of the members of 
its second argument, ordered so that the comparator returns 
true on adjacent members.*)

fun split z [] [] [] l3 = l3
  | split z [x] [] [] l3 = [x]
  | split z [] [x] [y] l3 =
	if (x < y)
	then ([x]@[y])
	else ([y]@[x])
  | split z [] (x::xs) [] l3 = ((split x (x::xs) [] [] [])@l3)
  | split z [] [] (x::xs) l3 = (l3@(split x (x::xs) [] [] []))
  | split z [] (x::xs) (y::ys) l3= (((split x (x::xs) [] [] [])@l3)@(split y (y::ys) [] [] []))
  | split z (x::xs) l1 l2 l3 = 
	if (x < z)
	then (split z xs (l1@[x]) l2 l3)
	else 
		if (x = z)
		then (split z xs l1 l2 (l3@[x]))
		else (split z xs l1 (l2@[x]) (l3@[x]));

fun mergesort comp [] =[]
  | mergesort comp (z::zs) = split z (z::zs) [] [] [];


(*Practice with datatypes - 15%

Define an ML datatype datatype either = ImAString of string | ImAnInt of int.
Define an ML datatype named eitherTree for binary trees containing values of type 
	either where data may be held at both interior and leaf nodes of the tree.
Define an ML function eitherSearch having 
	type eitherTree -> int -> bool 
	that returns true if the int is in the tree and false otherwise. 
The trick to getting this to type check is to realize that ImAnInt of int values and 
int values do not have the same type. But you can transform either into the other.
Define an ML function of no arguments, eitherTest that:

constructs an eitherTree with at least 5 int-containing leaves, 
at least 5 string-containing leaves, and at least 4 levels;
searches the tree using your eitherSearch function for an int that is present in the tree;
and, searches the tree using your eitherSearch function for 
a value that is notpresent in the tree.*)

datatype either = ImAString of string | ImAnInt of int;
datatype eitherTree = Empty | Leaf of either | Node of { left: eitherTree, f: either, right: eitherTree};
type ImAnInt = int -> int;
type ImAString = string -> string;

fun eitherSearch (Empty) x = false
  | eitherSearch (Node {left, f, right}) x = 
	if (f = x)
	then (true)
	else ((eitherSearch left x) orelse (eitherSearch right x))
  | eitherSearch (Leaf f) x = 
	if (f = x)
	then (true)
	else (false);

fun eitherTest ()= let
	val one = ImAnInt 1
	val two = ImAnInt 2
	val three = ImAnInt 3
	val four = ImAnInt 4
	val five = ImAnInt 5

	val a = ImAString "a"
	val b = ImAString "b"
	val c = ImAString "c"
	val d = ImAString "d"
	val e = ImAString "e"

	val l1 = Leaf one
	val l3 = Leaf three
	val l4 = Leaf four
	val l5 = Leaf five
	val le = Leaf e

	val nd = Node {left = l3, f = d, right = l4}
	val n2 = Node {left = Empty, f = two, right = l5}
	val nc = Node {left = l1, f = c, right = n2}
	val nb = Node {left = nd, f = b, right = le}	
	val na = Node {left = nb, f = a, right = nc}

	val Ts = [true, false]

	val v1 = ImAnInt 1
	val v2 = ImAnInt 7
	
	in
		if (([(eitherSearch na v1)]@[(eitherSearch na v2)]) = Ts)
		then true
		else false
	end;







datatype 'a Tree = LEAF of 'a | NODE of ('a Tree) list;

fun treeToString f (LEAF t) = f t
  | treeToString f (NODE t) = let
	fun nodes f [] = NONE
	| nodes f [x] = f x
	| nodes f (x::xs) = (nodes f x)^(nodes f xs)
	in
	nodes f t
	end;