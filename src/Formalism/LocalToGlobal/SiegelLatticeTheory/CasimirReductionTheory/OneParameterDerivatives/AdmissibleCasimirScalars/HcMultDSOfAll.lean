module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.CompactDerivativesBounded
public import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity
public import Formalism.SharpRestriction.CuspSpanNormBounds.ExpansionFromLemmaB
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.SG.Pf.admitted

open Formalism.MainNotions.S Formalism.REAL Formalism.MainNotions.BridgeCPX

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem casScalar_of (h1 : CalculusOnSmoothVectors) (h2 : CasimirProperties) (h3 : SchurSymmetricDense) : CasScalarStatement := by
  intro n ε H _ _ _ σ hσ hirr w hw
  have hstb : ∀ (g : UJ ε), ∀ v ∈ Vsub ε hσ w, σ (umat g) v ∈ Vsub ε hσ w := fun g v hv => Vsub_stable hσ w g hv
  obtain ⟨hadd, hsm, hsym, hinv⟩ := h2 n ε H σ _ (h1 n ε H σ hσ w) hstb
  exact h3 n ε H σ hσ hirr _ (Vsub_dense hσ hirr hw) hstb (Cas ε σ) hadd hsm hsym hinv

theorem hcMultDS_of (h0 : SmoothVectorsDense) (h1 : CalculusOnSmoothVectors) (hc : CasScalarStatement) (h4 : CasimirScalarBounded)
    (h5 : CompactDerivativesBounded) (h6 : SmallMotionNeighbourhood) (h7 : FormalDegreeFiniteDim) : HCMultDS := by
  intro n ε lam H _ _ _ σ hDS S hfd hst
  have hσ : IsURepOn (UJset ε) σ := hDS.2.2.1
  have hirr : IsIrredOn (UJset ε) σ := hDS.2.2.2.1
  haveI : Nontrivial H := hDS.2.1
  obtain ⟨w, hw⟩ := exists_ne (0 : H)
  obtain ⟨d, hd⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS lam σ hDS
  have hC : Calc ε σ (Vsub ε hσ w) := h1 n ε H σ hσ w
  obtain ⟨c, hcs⟩ := hc n ε H σ hσ hirr w hw
  obtain ⟨C, hK⟩ := h5 n ε H σ hσ S hfd hst
  obtain ⟨C', hb⟩ := h4 n ε H σ _ hC c hcs (isoK ε σ S) C hK
  obtain ⟨U, hU, hn⟩ := h6 n ε H σ _ hC (isoK ε σ S) C' hb (h0 n ε H σ hσ hirr w hw S hfd hst)
  exact h7 n ε H σ hσ d hd (isoK ε σ S) U hU hn

theorem hcMultDS_of_all (h0 : SmoothVectorsDense) (h1 : CalculusOnSmoothVectors) (h2 : CasimirProperties) (h3 : SchurSymmetricDense) (h4 : CasimirScalarBounded)
    (h5 : CompactDerivativesBounded) (h6 : SmallMotionNeighbourhood) (h7 : FormalDegreeFiniteDim) : HCMultDS :=
  hcMultDS_of h0 h1 (casScalar_of h1 h2 h3) h4 h5 h6 h7

theorem kFinSmooth_of (h : HCMultDS) : Formalism.MainNotions.LowestKTypeMultiplicity.KFinSmooth :=
  fun _ _ _ _ _ _ _ _ _ _ hσ _ hv => kfin_smoothVec (HCAdmDS_of_mult h) hσ hv

theorem kFinSmooth_of' (h : HCMultDS) : Formalism.MainNotions.DiscreteSeriesInnerProducts.KFinSmooth :=
  fun _ _ _ _ _ _ _ _ _ hσ _ hv => kfin_smoothVec (HCAdmDS_of_mult h) hσ hv

end Formalism.L2.SG.Pf.admitted
