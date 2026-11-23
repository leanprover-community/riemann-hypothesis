module

public import Development.EtaleCohomology.TateTwists.EtaleSheafificationSectionsLocallyFromPresheaf
public import Development.EtaleCohomology.TateTwists.EtaleSheafSectionsEqOfLocallyEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace LateralTheory.Fin.EtaleSheafificationSectionsLocallyFromPresheaf
theorem etale_sheaf_localization_properties_of_components : LateralTheory.EtaleFoundations.EtaleSheafificationSectionsLocallyFromPresheaf := by
  apply LateralTheory.EtaleFoundations.ShfLocPf.etale_sheaf_sections_eq_of_locally_eq
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleSheafificationSectionsLocallyFromPresheaf := etale_sheaf_localization_properties_of_components
end LateralTheory.Fin.EtaleSheafificationSectionsLocallyFromPresheaf
