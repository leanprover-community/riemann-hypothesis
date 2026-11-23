module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineBundleIntersectionNumberGroundFieldChangeStatement
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.ArInt

theorem nefFib_of_primeField : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (L : HermLB p),
    (∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (q : ℕ) [Fact q.Prime]
      [Algebra (ZMod q) Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod q) (L.B.pull i) 1) →
    ArInt.NefFib L := by
  intro k _ X p L h Z i _ _ κ _ _ _ hdim
  haveI : Fintype κ := Fintype.ofFinite κ
  haveI hq : Fact (ringChar κ).Prime := ⟨CharP.char_is_prime κ (ringChar κ)⟩
  letI : Algebra (ZMod (ringChar κ)) κ := ZMod.algebra κ (ringChar κ)
  letI : Algebra (ZMod (ringChar κ)) Γ(Z, ⊤) :=
    ((algebraMap κ Γ(Z, ⊤)).comp (algebraMap (ZMod (ringChar κ)) κ)).toAlgebra
  haveI : IsScalarTower (ZMod (ringChar κ)) κ Γ(Z, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  have h1 := h Z i (ringChar κ) hdim
  have e := GlobalTheory.T.lineBundleIntersectionNumber_groundFieldChange (ZMod (ringChar κ)) κ Z (structureModule Z) (fun _ : Fin 1 => L.B.pull i)
  rw [topSelf_def] at h1 ⊢
  rw [e] at h1
  haveI : Module.Finite (ZMod (ringChar κ)) κ := Module.Finite.of_finite
  have hpos : (0 : ℤ) < (Module.finrank (ZMod (ringChar κ)) κ : ℤ) := by
    exact_mod_cast Module.finrank_pos
  exact (mul_nonneg_iff_of_pos_left hpos).mp h1

end GlobalTheory.ArInt
