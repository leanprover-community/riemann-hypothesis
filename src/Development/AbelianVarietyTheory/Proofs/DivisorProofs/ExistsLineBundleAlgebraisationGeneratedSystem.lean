module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationMorphismsStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomEqOfPullSections
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsHomogeneousXPowMulAddXPowMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section

namespace GlobalTheory.FormalAlg

theorem exists_lb_of_generated_system_proper : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) → (∀ e, ⨆ i, nonzeroLocus (s e i) = ⊤) → ∃ (M : LB X.left) (s' : Fin (n + 1) → LB.Sec M) (w : ∀ e, LB.Iso (H e) (M.pull (b e))), M.IsLB ∧ ∀ e, (w e).IsGen ∧ ∀ j, Rel (b e) (w e) (s' j) (s e j) := by
  intro R _ _ I hcI X hX Y β b hb hbb H v hH n s hs hgen
  obtain ⟨P, f, O, t, hO, hva, hP⟩ := GlobalTheory.ProjQuot.exists_veryAmpleBy_of_ideal R n ⊥ (fun F hF d => by
    rw [Ideal.mem_bot] at hF ⊢
    rw [hF, map_zero])
  choose c w hc' hw hr using fun e => GlobalTheory.exists_hom_of_veryAmpleBy R P f O n t hO hva _
    ((Y e).hom ≫ thick R I e) (H e) (s e) (hH e).1 (hgen e) (fun d F hF h k => by
      obtain ⟨m, hm⟩ := (hP d F hF).1 h 0
      have : F = 0 := by
        rw [Ideal.mem_bot] at hm
        exact ((MvPolynomial.isRegular_X (n := (0 : Fin (n + 1)))).pow m).left (by simpa using hm)
      rw [this, map_zero])
  have c₁ : ∀ e, β e ≫ (Y (e + 1)).hom ≫ thick R I (e + 1) = (Y e).hom ≫ thick R I e := fun e => by
    rw [← (hb (e + 1)).w, ← Category.assoc, hbb, (hb e).w]
  have hcc : ∀ e, β e ≫ c (e + 1) = c e := fun e => by
    have hv := (isGen_iff _).1 (hH e).2
    have hw' := (isGen_iff _).1 (hw (e + 1))
    obtain ⟨w'', T⟩ := exists_comp (hH (e + 1)).1 (w (e + 1)) (v e) hw' hv hO (hH e).1
    exact GlobalTheory.MapUniq.hom_eq_of_pull_sections R P f O n t hO hva _ (H e) (s e) _ _ w'' (w e) (hH e).1
      (by rw [Category.assoc, hc', hc', c₁]) ((isGen_iff _).2 (T.pgen_comp (hH (e + 1)).1 hw' hv)) (hw e)
      (fun j => Rel.comp T (hH (e + 1)).1 (hr (e + 1) j) (hs e j)) (hr e)
  haveI hPp : IsProper f := GlobalTheory.AbLaw.isProper_of_isProjBy R P f ⟨O, hO, n, t, hva⟩
  obtain ⟨g, hg, -⟩ := GlobalTheory.T.formalAlgebraisation_morphisms' R I hcI X (Over.mk f) hX (inferInstanceAs (IsSeparated f))
    (inferInstanceAs (LocallyOfFiniteType f)) (inferInstanceAs (QuasiCompact f)) Y β b hb hbb
    c hc' hcc
  have hM : (O.pull g.left).IsLB := LB.isLB_pull hO _
  obtain ⟨s', hs'⟩ := GlobalTheory.MorAlg.exists_isPull g.left hO t
  have key : ∀ e, GlobalTheory.MorAlg.IsPull (b e) s' (s e) := fun e =>
    GlobalTheory.MorAlg.IsPull.cancel hO hM (hH e).1 hs' (by rw [hg e]; exact ⟨w e, hw e, hr e⟩)
  choose w' hw' cw using key
  exact ⟨O.pull g.left, s', w', hM, fun e => ⟨hw' e, fun j => cw e j⟩⟩

end GlobalTheory.FormalAlg
