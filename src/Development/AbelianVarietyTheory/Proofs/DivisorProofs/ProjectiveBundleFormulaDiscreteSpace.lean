module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteGlBundleEqTrivialGLBundleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyProjectiveBundleFormula
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveCochainModelTrivialProjectiveBundStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveComplexMapQuasiIsoOfUnitSchemesStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

theorem inv_sch (q : ℕ) (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) : Inv q (sch.obj U) := by
  intro U' ⟨f⟩
  simpa using hU.map f.appTop.hom

theorem pbf_disc : ∀ (q : ℕ) [NeZero q] (N : ℕ) (F : PSh) (V : disc.obj F ⟶ ofCat (glCat N)),
    Inv q (disc.obj F) → PBF q V := by
  intro q _ N F V hF n i
  obtain ⟨J, ψ, hJ, hinj, he⟩ := GlobalTheory.T.exists_injective_cochainModel_trivialProjectiveBundle q N i
  have key := GlobalTheory.T.injectiveComplexMap_quasiIso_of_unit_schemes q (fun j : Fin N => res (ZMod q) (tw q (i - (j : ℕ)))) J (fun j => 2 * ((j : ℕ) : ℤ)) ψ 0
    (fun j => inferInstanceAs ((injectiveResolution (tw q (i - (j : ℕ)))).cochainComplex.IsStrictlyGE 0)) hJ
    (fun j m => inferInstanceAs (Injective ((injectiveResolution (tw q (i - (j : ℕ)))).cochainComplex.X m))) hinj
    (by
      intro U hU m
      obtain ⟨e, he'⟩ := he (yoneda.obj U) (inv_sch q U hU) m
      have hs := GlobalTheory.T.etaleCohomology_projectiveBundle_formula q U (trivV N (sch.obj U)) (inv_sch q U hU) m i
      have hcomp : (fun a : ∀ j : Fin N, Ht q (sch.obj U) (m - 2 * (j : ℕ)) (i - (j : ℕ)) =>
          ∑ j : Fin N, ((cup q (pull _ (pullback.fst (trivV N (sch.obj U)) (PGL.pr N)) _ _ (a j))
            (cpow q (c1 q (pullback.snd (trivV N (sch.obj U)) (PGL.pr N) ≫ PGL.line N)) j)).cast (by ring) (by ring) :
              Ht q _ m i)) = e ∘ (fun a => ∑ j, cpost _ (ψ j) (m - 2 * (j : ℕ)) m (by omega) (a j)) :=
        funext fun a => (he' a).symm
      rw [hcomp] at hs
      exact (Function.Bijective.of_comp_iff' e.bijective _).1 hs)
    F hF n
  obtain ⟨e, he'⟩ := he F hF n
  rw [GlobalTheory.T.discrete_glBundle_eq_trivialGLBundle N F V]
  have hcomp : pbfMap q (trivV N (disc.obj F)) n i =
      e ∘ (fun a => ∑ j, cpost _ (ψ j) (n - 2 * (j : ℕ)) n (by omega) (a j)) :=
    funext fun a => (he' a).symm
  rw [hcomp]
  exact e.bijective.comp key

end GlobalTheory.EtC

end
