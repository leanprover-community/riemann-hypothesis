module

public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalRingCardinality.DataHost
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

namespace CharEx

section Sub

variable {L : Type} [Field L] [NumberField L] (F : Type) [Field F] [NumberField F] [Algebra F L]

def aF (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : Ideles L :=
  ∏ P ∈ aboveF (L := L) F v, localIdele L P (atFin P (upF F k))

def aFi (w : InfinitePlace F) (k : Fˣ) : Ideles L :=
  ∏ w' ∈ aboveInf (L := L) F w, infIdele L w' (atInf w' (upF F k))

theorem resFin_eq (χ : HChar L) (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : χ.resFin v k = χ.1 (aF F v k) := by
  unfold HChar.resFin aF
  rw [map_prod, MonoidHom.finsetProd_apply]
  exact Finset.prod_congr rfl fun P _ => rfl

theorem resInf_eq (χ : HChar L) (w : InfinitePlace F) (k : Fˣ) : χ.resInf w k = χ.1 (aFi F w k) := by
  unfold HChar.resInf aFi
  rw [map_prod, MonoidHom.finsetProd_apply]
  exact Finset.prod_congr rfl fun w' _ => rfl

end Sub


variable {L : Type} [Field L] [NumberField L]


variable {R : Formalism.BasicNotions.Ranks} {H : Formalism.BasicNotions.Host R}

end CharEx

end Formalism.L2.Host
