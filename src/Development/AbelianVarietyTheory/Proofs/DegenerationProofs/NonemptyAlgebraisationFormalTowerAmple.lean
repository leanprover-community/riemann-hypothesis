module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosedPointMemRange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAbelianSchemeOfAbelianThickeningsStatement
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.TowerAlg

theorem isPullback_of_grp {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [GrpObj B'] {f : S' ⟶ S}
    {F : B'.left ⟶ B.left} (h : IsGrpPullback B' B f F) : IsPullback F B'.hom B.hom f := h.1

theorem exists_alg (hG : GlobalFnsSt) (hE : Ega) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}
    (hA : admitted R I) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) [∀ e, GrpObj (Y e)]
    [∀ e, IsCommMonObj (Y e)] (hY : ∀ e, IsAbelianScheme (Y e)) (N : ∀ e, CP (Y e))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (h : ∀ e, IsCPPullback (N e) (N (e + 1)) (thickTrans R I e) (β e))
    (hamp : RelAmple (Y 0) (N 0).L.L) :
    ∃ (B : Over (Spec (CommRingCat.of R))) (_ : GrpObj B) (_ : IsCommMonObj B) (Q : CP B)
      (b : ∀ e, (Y e).left ⟶ B.left), IsAbelianScheme B ∧ RelAmple B Q.L.L ∧
      (∀ e, IsCPPullback (N e) Q (thick R I e) (b e)) ∧ ∀ e, β e ≫ b (e + 1) = b e := by
  have hN : IsNoetherianRing R := hA.1.1
  have hI : I ≠ ⊤ := hA.2.2.2.1.ne_top
  have hc : IsAdicComplete I R := hA.1.2.2.2
  choose hβ v hv using h
  obtain ⟨B, M, b, hp, hs, hM, ha, hb, hβb, hiso⟩ := hE.1 R I hI hc hA.2.1 Y β
    (fun e => (N e).L.L) v (fun e => isPullback_of_grp (hβ e)) (fun e => (hY e).smooth)
    (fun e => ⟨(N e).L.isLB, (hv e).gen⟩) hamp
  obtain ⟨g, hB, hg⟩ := GlobalTheory.T.isAbelianScheme_of_abelian_thickenings hE R I hA Y β hY hβ B b hp hs hb hβb
  have c := hB.comm
  obtain ⟨Q, hQ, hq⟩ := exists_cp_alg hG hE.2.2.1 hI hc N hB hp hg hM hiso hY
  exact ⟨B, g, c, Q, b, hB, by rw [hQ]; exact ha, hq, hβb⟩

theorem nonempty_alg : Laws → Laws2 → Ega → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G) (X : Type) [AddCommGroup X] (T : TowerR I P X), RelAmple (T.l 0).Q.B (T.l 0).D.M.L.L → Nonempty T.Alg := by
  intro hL _ hE R _ _ _ I hA G _ _ P X _ T hamp
  obtain ⟨B, _, _, Q, b, h₁, h₂, h₃, h₄⟩ := exists_alg hL.globalFns hE hA (fun e => (T.l e).Q.B)
    (fun e => (T.l e).Q.isAb) (fun e => (T.l e).D.M) T.β T.β_pb hamp
  exact ⟨⟨B, h₁, Q, h₂, b, h₃, h₄⟩⟩

end GlobalTheory.TowerAlg
end
