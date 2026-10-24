import Compact.WF.Enum

/-! 構文的な補題の主張の総当たり検査（`lake env lean Compact/WF/Test.lean` で実行。ライブラリには入れない）。
各検査は反例の先頭を返す（空なら成り立つ）。 -/

open RTKA

-- 反射性（全ての項）
#eval firstFails 3 (nfList 2 7) (fun t => cmp t t == .eq)
-- 反対称性・相等（標準形、大きさ ≤ 6）
#eval firstFails 3 (pairs (nfList 2 6)) (fun (a, b) => cmp b a == (cmp a b).swap)
#eval firstFails 3 (pairs (nfList 2 6)) (fun (a, b) => cmp a b != .eq || a == b)
-- 推移性（大きさ ≤ 5）
#eval transFails (nfList 2 5)
