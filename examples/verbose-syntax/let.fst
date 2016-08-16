module Let

let f = begin
  let x = 1 in
  let y = 2 in
  x + y + 3 end

let g a =
  let x = 1 in
  let y = 2 in
  a + x + y
