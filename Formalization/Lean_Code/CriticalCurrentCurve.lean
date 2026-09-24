import Lean_Code.RegularizedLocalSmoothing
import Lean_Code.SmoothCriticalCurrent

/-!
This compatibility module intentionally contains no additional declarations.
The endpoint current is handled directly through the continuous critical
pairing in `SmoothCriticalCurrent`; keeping a second, elaboration-heavy `Lp`
lift here made clean builds depend on stale object files.
-/
