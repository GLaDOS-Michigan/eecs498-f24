datatype Card = Shelf | Patron(name: string)
datatype Book = Book(title: string)
type Variables = map<Book, Card>    // our Library state

ghost predicate Init(v: Variables) {
  forall book | book in v :: v[book] == Shelf
}

ghost predicate CheckOut(v:Variables, v':Variables, book:Book, patron:string) {
  && book in v
  && v[book] == Shelf
  && (forall book | book in v :: v[book] != Patron(patron))
  && v' == v[book := Patron(patron)]
}

ghost predicate CheckIn(v:Variables, v':Variables, book:Book, patron:string) {
  && book in v
  && v[book] == Patron(patron)
  && v' == v[book := Shelf]
}

ghost predicate Next(v:Variables, v':Variables) {
  || (exists book, patron :: CheckIn(v, v', book, patron))
  || (exists book, patron :: CheckOut(v, v', book, patron))
}

ghost predicate Safety(v:Variables) {
  
}

lemma SafetyProof()
  ensures forall v | Init(v) :: Safety(v)
  ensures forall v, v' | Safety(v) && Next(v, v') :: Safety(v')
{
  
}