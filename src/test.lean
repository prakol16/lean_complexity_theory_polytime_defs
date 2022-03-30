import computability.primrec
import computability.encoding
import data.num.basic

set_option pp.implicit true

#check (infer_instance : primcodable (list ℕ))
#eval encodable.encode [5, 5, 5]

#check (infer_instance : encodable (list ℕ))
#check encodable.list

def pos_num.to_list : pos_num → list bool
| pos_num.one := []
| (pos_num.bit0 xs) := ff :: (pos_num.to_list xs)
| (pos_num.bit1 xs) := tt :: (pos_num.to_list xs)

-- #eval pos_num.of_nat 23452300002

#eval (match num.of_nat' 23452300002 with 
    | num.zero := []
    | (num.pos x) := x.to_list ++ [tt]
  end : list bool)
-- #eval (cast rfl (computability.encoding_nat_bool.encode 2345230) : list bool)
