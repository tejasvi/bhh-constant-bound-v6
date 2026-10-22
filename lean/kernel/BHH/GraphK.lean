/-
Track K: the g tables `gtK 3`, `gtK 4` (BHHCert/GTabK.lean, the same values as `gtN 3`, `gtN 4`) are sound, by
kernel evaluation (`decide +kernel`, no `native_decide`) of the table check `checkTab` (soundness: `checkTab_sound`).
k = 4 takes about 50 s of kernel time on one core.
-/
import BHH.Graph
import BHHCert.GTabK

namespace BHH.E

open BHH.Cert

set_option maxRecDepth 100000 in
theorem gtK_check_three : checkTab 3 (gtK 3).gmin = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem gtK_check_four : checkTab 4 (gtK 4).gmin = true := by decide +kernel

theorem gtK_sound_three : GTabSound 3 (gtK 3) := checkTab_sound (by norm_num) (gtK 3) gtK_check_three

theorem gtK_sound_four : GTabSound 4 (gtK 4) := checkTab_sound (by norm_num) (gtK 4) gtK_check_four

end BHH.E

namespace BHH

-- the deliverables of this file, also under `BHH` (helpers stay in `BHH.E`)
export E (gtK_check_three gtK_check_four gtK_sound_three gtK_sound_four)

end BHH
