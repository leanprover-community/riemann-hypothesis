module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
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

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.LocalSituation TensorProduct GlobalTheory.Per GlobalTheory.Prism

namespace GlobalTheory.Published

def BhattScholzeCrystallineLattices : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P₀ : Obj l ↥(OL K)) (e : P₀.A ≃+* Ainf l), IsAinf K P₀ e →
    (∀ (P : LocPrime l) (AI : LocAinf l P), IsStd P AI →
      ∀ (LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ →
        letI := zlMod LL T
        ∃ (E : FCrys l ↥(OL K))
          (j : E.M P₀ →ₛₗ[(inclW l).comp e.toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)),
          Realises K E P₀ e ↥T.L.T (fun g => actTZ LL T g) j) ∧
    (∀ (T T' : Type) [AddCommGroup T] [Module ℤ_[l] T] [AddCommGroup T'] [Module ℤ_[l] T']
      (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (ρ' : ↥(GK K) → (T' →ₗ[ℤ_[l]] T'))
      (E E' : FCrys l ↥(OL K))
      (j : E.M P₀ →ₛₗ[(inclW l).comp e.toRingHom] (WCb l ⊗[ℤ_[l]] T))
      (j' : E'.M P₀ →ₛₗ[(inclW l).comp e.toRingHom] (WCb l ⊗[ℤ_[l]] T')),
      Realises K E P₀ e T ρ j → Realises K E' P₀ e T' ρ' j' →
      ∀ f : T →ₗ[ℤ_[l]] T', (∀ g x, f (ρ g x) = ρ' g (f x)) →
        ∃! u : FHom E E', ∀ x, j' (u.u P₀ x) = f.lTensor (WCb l) (j x))

end GlobalTheory.Published
