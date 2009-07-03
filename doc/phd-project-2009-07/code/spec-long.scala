assert(
  forAll((xs: List[Int]) =>
  forAll((ys: List[Int]) =>
  forAll((z: Int) => {
    (content(xs) == content(ys)) ==> (content(insert(z, xs)) == content(insert(z, ys)))
  })))
)
