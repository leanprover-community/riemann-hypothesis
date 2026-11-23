module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingHeckePointsPowEqOneStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommutatorPairingValueHeckePointsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchemeRootOfUnityEqOneOfGeometricPointsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingHeckePointsGeometricEqOneStatement
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Hecke

theorem weilIs_heckeSub_one : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h₁ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ h₂ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 h₂) 1 := by
  intro p _ D R _ b g c k N hc hk hN hNp hEF hg hck S s o h₁ hh₁ h₂ hh₂
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_commutatorPairing_value_heckePoints p D R b g c k N hc hk hN hNp hEF hg hck S s o h₁ hh₁ h₂ hh₂
  have hQ : (lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o.isLB _ _
  have hA2 : IsAbelianScheme (G2 o.A) :=
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have h1 : u = 1 := by
    refine GlobalTheory.T.scheme_rootOfUnity_eq_one_of_geometric_points R S s k u (b.unit k hk)
      (GlobalTheory.T.commutatorPairing_heckePoints_pow_eq_one p D R b g c k N hc hk hN hNp hEF hg hck S s o h₁ hh₁ h₂ hh₂ u hu) ?_
    intro K _ _ x β hx
    have hp := GlobalTheory.CommPairing.weilIs_pull (A := G2 o.A) GlobalTheory.globalFns_holds hA2 hQ (toUnit (Over.mk x)) hu
    exact GlobalTheory.T.weilPairing_heckePoints_geometric_eq_one p D R b g c k N hc hk hN hNp hEF hg hck S s o h₁ hh₁ h₂ hh₂ K x β hx _ hp
  subst h1
  exact hu

end GlobalTheory.UPel.HT.Hecke
