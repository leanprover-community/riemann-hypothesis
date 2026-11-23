module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRules
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.RootLoc

theorem root_loc_pow_prim : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ ω : (Γ(U, ⊤))ˣ, ω ^ q = 1 →
    Loc U fun V g => ∃ (ζ : Prim q Γ(V, ⊤)) (a : ℕ), (Units.map g.appTop.hom.toMonoidHom ω : Γ(V, ⊤)) = ζ.1 ^ a := by
  intro q _ U hq ω hω
  apply GlobalTheory.EtC.loc_trans
  refine GlobalTheory.EtC.loc_mono _ _ _ ((PrimLoc.prim_loc q U).1 hq) ?_
  rintro V g ⟨ζ⟩
  have hx : (g.appTop.hom (ω : Γ(U, ⊤))) ^ q = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hω, Units.val_one, map_one]
  refine GlobalTheory.EtC.loc_mono _ _ _ ((PrimLoc.prim_loc q V).2.2.1 ζ _ hx) ?_
  rintro W k ⟨a, ha⟩
  refine ⟨ζ.map k.appTop.hom, a, ?_⟩
  rw [Units.coe_map]
  exact (PrimLoc.appTop_comp g k _).trans ha

end GlobalTheory.EtC.RootLoc
