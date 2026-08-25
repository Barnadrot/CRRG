example : ((1900 : Rat) / 4096) ≤ 1 := by native_decide
#eval ((1900 : Rat) / 4096).num
#eval ((1900 : Rat) / 4096).den
example : ((1900 : Rat) / 4096).num ≤ 1024 := by decide
example : (1900 : Rat) / 4096 = 475 / 1024 := by rfl
#check @Rat.le_trans
#check @Rat.num_le_num
#check @Rat.le_def
