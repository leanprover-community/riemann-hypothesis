module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedPre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLiftHomAffinePairStatement
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

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem exists_lift_pair_natTrans (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R)
    (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ)
    (m : IsMor D.κ D.t D'.κ D'.t σ φ₀) (hi : φ₀ ≫ D.i = D'.i ≫ φ) :
    ∃ θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G, ∀ (p : (Pair φ)ᵒᵖ) a,
      (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) =
        Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a) := by
  choose θ hθ using GlobalTheory.T.exists_smoothLift_hom_affinePair D D' Λ Λ' σ φ φ₀ hφ m hi
  refine ⟨⟨fun p ↦ θ p.unop, fun p q a ↦ ?_⟩, fun p a ↦ hθ p.unop a⟩
  apply Thick.Hom.ext'
  apply AlgHom.ext
  intro b
  obtain ⟨x, rfl⟩ := (Λ.e (Opposite.op p.unop.1.2)).surjective b
  have h1 := Λ.nat ((pairSnd φ).map a) x
  have h2 := hθ q.unop (mp (OAff D.s) ((pairSnd φ).map a) x)
  have h3 := hθ p.unop x
  have h4 := Λ'.nat ((pairFst φ).map a) (GlobalTheory.CechDR.secPull D.s D'.s p.unop x)
  have h5 := (pairPull hφ).naturality a x
  exact ((congrArg (θ q.unop).φ h1.symm).trans h2).trans
    ((congrArg (Λ'.e (Opposite.op q.unop.1.1)) h5).trans
      (h4.trans (congrArg (Λ'.L.map ((pairFst φ).map a)).φ h3.symm)))

end GlobalTheory.PDForm
