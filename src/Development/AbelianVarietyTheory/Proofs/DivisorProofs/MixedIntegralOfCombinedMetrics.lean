module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PnPosOfGeneratesAt
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CombChern

section Bundle

variable {X : Scheme.{0}} [IsIntegral X]

theorem presents_zpow {D : CartierDiv X} {L : LB X} {r : L.ι → X.functionFieldˣ} (h : Presents D L r) (n : ℤ) :
    Presents (n • D) (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n) fun j => r (j PUnit.unit) ^ n := by
  have mem : ∀ (j : PUnit → L.ι) {x : X}, x ∈ (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n).U j →
      x ∈ L.U (j PUnit.unit) := fun j x hx => by simpa using Set.mem_iInter.1 hx PUnit.unit
  refine ⟨LB.isLB_linComb h.isLB _ _, fun j j' hjj => ?_, fun j x hx => (h.isEqn _ x (mem j hx)).zsmul n⟩
  have l : (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n).U j ⊓
      (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n).U j' ≤ L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit) :=
    fun x hx => ⟨mem j hx.1, mem j' hx.2⟩
  have hg : (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n).g j j' = res l (L.g (j PUnit.unit) (j' PUnit.unit)) ^ n := by
    change ∏ _k : PUnit, _ = _
    exact Fintype.prod_unique _
  have key : ∀ {U : X.Opens} (hU : genericPoint X ∈ U) (u : Γ(X, U)ˣ) (m : ℤ),
      fnOf U hU ((u ^ m : Γ(X, U)ˣ) : Γ(X, U)) = fnOf U hU (u : Γ(X, U)) ^ m := fun hU u m => by
    have e := congrArg Units.val (map_zpow (Units.map (fnOf _ hU).toMonoidHom) u m)
    rw [Units.val_zpow_eq_zpow_val, Units.coe_map, Units.coe_map] at e
    exact e
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, h.isRatSec _ _ (l hjj), mul_zpow, hg, key]
  congr 2
  exact (fnOf_resG l hjj _).symm

end Bundle

section Comb

variable {X : Scheme.{0}} [IsIntegral X] {ι : Type} (T : ι → LB X) (b : ι → ℤ)

variable {k : Type} [CommRing k] {p : X ⟶ Sp k} {σ : k →+* ℂ}

end Comb

section Met

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

end Met

end GlobalTheory.CombChern
