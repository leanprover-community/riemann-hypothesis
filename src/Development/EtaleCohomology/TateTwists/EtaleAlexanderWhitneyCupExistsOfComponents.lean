module

public import Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupCochainExistsForPairing
public import Development.EtaleCohomology.TateTwists.EtaleCochainDifferentialEvaluationDegreeZero
public import Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupLeibnizOfPairing
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.TypeStar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupCochainExistsHolds, Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyLeibnizEvalDegreeZero, Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyLeibnizOfSucc, Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyLeibnizSuccHolds, Development.EtaleCohomology.TateTwists.FreeExt, Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyUniquenessHolds, Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupExistsOfComponents

-- ===== clump member: Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupCochainExistsHolds =====
-- clump-header: {"m": "Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupCochainExistsHolds", "h": "module\n\npublic import Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupCochainExistsForPairing\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem awex_sub_res {E : Spc} {N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.res g).sub j l h = (x.sub j l h).res g := by
  unfold Sx.sub Sx.res
  exact ((E.map (SimplexCategory.subinterval j l h).op).naturality_apply g.op x)

theorem awex_freeGen_res {R : Type} [CommRing R] (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    (((free R).obj P).obj.map g.op).hom (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  unfold freeGen
  have e := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)) (ModuleCat.freeMk (ULift.up x))
  refine e.symm.trans ?_
  exact congrArg (fun y => ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom y)
    (ModuleCat.free_map_apply (R := ULift.{1} R) (uliftFunctor.{1}.map (P.map g.op)) (ULift.up x))

theorem awex_ev_res {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (ev α p s h U x) = ev α p s h V (x.res g) := by
  unfold ev Sec.res
  have e := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    ((((chainsXIso R E p).inv ≫ α.v _ _ h).hom).naturality g.op)) (freeGen R _ U x)
  refine e.symm.trans ?_
  exact congrArg (fun y => (((chainsXIso R E p).inv ≫ α.v _ _ h).hom.app (op V)).hom y)
    (awex_freeGen_res (R := R) _ g x)

theorem awex_lift_single {S : Type*} [Semiring S] {X M : Type*} [AddCommMonoid M] [Module S M]
    (f : X → M) (x : X) : Finsupp.lift M S X f (Finsupp.single x 1) = f x := by
  simp

noncomputable def awexNat {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) : (freeP R).obj (E.obj (op (SimplexCategory.mk p))) ⟶ (I.X s).obj where
  app U := ModuleCat.ofHom (Finsupp.lift _ (ULift.{1} R) _
        (fun y : ULift.{1} (Sx E p (unop U)) => a p s h (unop U) y.down))
  naturality := by
        intro U V g
        refine ModuleCat.hom_ext (Finsupp.lhom_ext' fun y => LinearMap.ext_ring ?_)
        have e := ModuleCat.free_map_apply (R := ULift.{1} R)
          (uliftFunctor.{1}.map ((E.obj (op (SimplexCategory.mk p))).map g)) y
        change (Finsupp.lift _ (ULift.{1} R) _ _) (((freeP R).obj _).map g |>.hom (Finsupp.single y 1)) =
          ((I.X s).obj.map g).hom ((Finsupp.lift _ (ULift.{1} R) _ _) (Finsupp.single y 1))
        erw [e]
        refine (awex_lift_single (S := ULift.{1} R) _ _).trans ?_
        refine Eq.trans ?_ (congrArg ((I.X s).obj.map g).hom (awex_lift_single (S := ULift.{1} R) _ _).symm)
        exact (ha p s h (unop V) (unop U) g.unop y.down).symm

noncomputable def awexPhi {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) : (free R).obj (E.obj (op (SimplexCategory.mk p))) ⟶ I.X s :=
  ((sheafificationAdjunction Scheme.etaleTopology _).homEquiv _ (I.X s)).symm (awexNat a ha p s h)

theorem awexPhi_freeGen {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ((awexPhi a ha p s h).hom.app (op U)).hom (freeGen R _ U x) = a p s h U x := by
  have e := toSheafify_sheafifyLift Scheme.etaleTopology (awexNat a ha p s h) (I.X s).property
  have e2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (congrArg (fun φ => φ.app (op U)) e))
    (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x))
  refine e2.trans ?_
  exact awex_lift_single (S := ULift.{1} R) (fun y : ULift.{1} (Sx E p U) => a p s h U y.down) (ULift.up x)

def EtaleSimplicialCochainFromNaturalEvaluationsExists : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
  (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
  (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) →
  ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x

theorem etale_alexander_whitney_cup_exists_of_cochain_from_evaluations (hmk : EtaleSimplicialCochainFromNaturalEvaluationsExists) : EtaleAlexanderWhitneyCupCochainExistsForPairing := by
  intro R _ I J K μ E n m k hk α β
  obtain ⟨γ, hγ⟩ := hmk R (E := E) (I := K) (n := k)
    (fun N w h U x => ∑ p : Fin (N + 1), (m * (p : ℕ)).negOnePow • μ.mul U (-((p : ℕ) : ℤ) + n)
      (-((N - p : ℕ) : ℤ) + m) w (by omega)
      (ev α p _ rfl U (x.sub 0 p (by omega))) (ev β (N - p) _ rfl U (x.sub p (N - p) (by omega))))
    (by
      intro N w h V U g x

      simp only [Sec.res, map_sum, Units.smul_def, map_zsmul]
      refine Finset.sum_congr rfl fun p _ => ?_
      congr 1
      rw [awex_sub_res, awex_sub_res, ← awex_ev_res, ← awex_ev_res]
      exact μ.nat g _ _ _ _ _ _)
  exact ⟨γ, fun N w h U x => hγ N w h U x⟩

noncomputable def awexCochain {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) :
    Cochain ((chains R).obj E) I n :=
  Cochain.mk fun x y hxy => if hx : x ≤ 0 then
    (((chains R).obj E).XIsoOfEq (show x = -(((-x).toNat : ℕ) : ℤ) by omega)).hom ≫
      (chainsXIso R E (-x).toNat).hom ≫ awexPhi a ha (-x).toNat y (by omega)
  else 0

theorem awex_key {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (q p : ℕ) (e : q = p) (he : -(p : ℤ) = -(q : ℤ)) (s : ℤ) (h : -(p : ℤ) + n = s) (hq : -(q : ℤ) + n = s) :
    (chainsXIso R E p).inv ≫ (((chains R).obj E).XIsoOfEq he).hom ≫ (chainsXIso R E q).hom ≫ awexPhi a ha q s hq =
      awexPhi a ha p s h := by
  subst e
  simp

theorem awex_ev {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (awexCochain a ha) p s h U x = a p s h U x := by
  unfold ev
  rw [awexCochain, Cochain.mk_v, dite_eq_left (by omega), awex_key a ha _ p (by omega)]
  exact awexPhi_freeGen a ha p s h U x

theorem etale_simplicial_cochain_from_natural_evaluations_exists_holds : EtaleSimplicialCochainFromNaturalEvaluationsExists := by
  intro R _ E I n a ha
  exact ⟨awexCochain a ha, awex_ev a ha⟩

theorem etale_alexander_whitney_cup_cochain_exists_holds : EtaleAlexanderWhitneyCupCochainExistsForPairing :=
  etale_alexander_whitney_cup_exists_of_cochain_from_evaluations etale_simplicial_cochain_from_natural_evaluations_exists_holds

end LateralTheory.EtaleFoundations
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupCochainExistsHolds =====

-- ===== clump member: Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyLeibnizEvalDegreeZero =====
-- clump-header: {"m": "Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyLeibnizEvalDegreeZero", "h": "module\n\npublic import Development.EtaleCohomology.TateTwists.EtaleCochainDifferentialEvaluationDegreeZero\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem etale_cup_alexanderWhitney_leibniz_eval_degree_zero : EtaleCochainDifferentialEvaluationDegreeZero := by
  intro R _ E I n m hm α U x w w' h h'
  subst h h'
  have hz : IsZero (((chains R).obj E).X (-((0 : ℕ) : ℤ) + 1)) :=
    HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by
      have e : ComplexShape.embeddingDownNat.f i = -(i : ℤ) := rfl
      omega)
  have hd0 : ((chains R).obj E).d (-((0 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ) + 1) = 0 := hz.eq_of_tgt _ _
  unfold ev
  rw [δ_v n m hm α (-((0 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ) + m) rfl (-((0 : ℕ) : ℤ) + n) (-((0 : ℕ) : ℤ) + 1)
    (by omega) rfl, hd0, zero_comp, smul_zero, add_zero, ← Category.assoc]
  rfl

theorem etale_cup_alexanderWhitney_leibniz_of_ext_and_succ (h0 : EtaleSimplicialCochainEqOfEvaluationsAgree) (hs : EtaleAlexanderWhitneyLeibnizPositiveSimplexDegree) :
    EtaleAlexanderWhitneyCupLeibnizRule :=
  etale_alexander_whitney_leibniz_of_ext_degree_zero_succ h0 etale_cup_alexanderWhitney_leibniz_eval_degree_zero hs

end LateralTheory.EtaleFoundations
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyLeibnizEvalDegreeZero =====

-- ===== clump member: Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyLeibnizOfSucc =====
-- clump-header: {"m": "Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyLeibnizOfSucc", "h": "module\n\npublic import Development.EtaleCohomology.TateTwists.EtaleCochainDifferentialEvaluationDegreeZero\npublic import Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyLeibnizEvalDegreeZero\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem awleib_ext_pf : EtaleSimplicialCochainEqOfEvaluationsAgree := by
  intro R _ E K k γ γ' H
  apply Cochain.ext
  intro p q hpq
  by_cases hp : ∃ N : ℕ, -(N : ℤ) = p
  · obtain ⟨N, rfl⟩ := hp
    rw [← cancel_epi (chainsXIso R E N).inv]
    apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _ (K.X q).property
    ext U : 2
    apply ModuleCat.free_hom_ext
    intro x
    exact H N q hpq U.unop x.down
  · have hz : IsZero (((chains R).obj E).X p) :=
      HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => hp ⟨i, by
        have e : ComplexShape.embeddingDownNat.f i = -(i : ℤ) := rfl
        omega⟩)
    exact hz.eq_of_src _ _

theorem etale_cup_alexanderWhitney_leibniz_of_succ (hs : EtaleAlexanderWhitneyLeibnizPositiveSimplexDegree) : EtaleAlexanderWhitneyCupLeibnizRule :=
  etale_cup_alexanderWhitney_leibniz_of_ext_and_succ awleib_ext_pf hs

end LateralTheory.EtaleFoundations
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyLeibnizOfSucc =====

-- ===== clump member: Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyLeibnizSuccHolds =====
-- clump-header: {"m": "Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyLeibnizSuccHolds", "h": "module\n\npublic import Development.EtaleCohomology.TateTwists.EtaleCochainDifferentialEvaluationDegreeZero\npublic import Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupLeibnizOfPairing\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem etale_cup_alexanderWhitney_leibniz_succ_holds : EtaleAlexanderWhitneyLeibnizPositiveSimplexDegree := by
  intro R _ I J K μ E n m k n₁ m₁ k₁ hk hn hm hk₁ hk₂ α β γ γ₁ γ₂ ha h1 h2 P w h U x
  subst hn hm
  obtain rfl : k₁ = k + 1 := by omega
  have e := LateralTheory.EtaleFoundations.etaleAlexanderWhitneyCup_leibniz_of_pairing R μ hk α β γ γ₁ γ₂ ha h1 h2
  rw [e, ev_add', awleib_ev_smul]

end LateralTheory.EtaleFoundations
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyLeibnizSuccHolds =====

-- ===== clump member: Development.EtaleCohomology.TateTwists.FreeExt =====
-- clump-header: {"m": "Development.EtaleCohomology.TateTwists.FreeExt", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.AwExPf

variable {R : Type} [CommRing R]

theorem free_ext (P : PSh) (F : Shv R) (φ ψ : (free R).obj P ⟶ F)
    (h : ∀ U x, Sec.map φ (freeGen R P U x) = Sec.map ψ (freeGen R P U x)) : φ = ψ := by
  let φ' : (presheafToSheaf Scheme.etaleTopology _).obj ((freeP R).obj P) ⟶ F := φ
  let ψ' : (presheafToSheaf Scheme.etaleTopology _).obj ((freeP R).obj P) ⟶ F := ψ
  change φ' = ψ'
  apply ((sheafificationAdjunction Scheme.etaleTopology _).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine NatTrans.ext (funext fun U => ModuleCat.free_hom_ext fun x => ?_)
  exact h U.unop x.down

theorem ev_ext {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n)
    (h : ∀ p s h U x, ev α p s h U x = ev β p s h U x) : α = β := by
  refine Cochain.ext _ _ (fun i j hij => ?_)
  by_cases hi : 0 ≤ -i
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
    rw [← cancel_epi (chainsXIso R E p).inv]
    exact free_ext _ _ _ _ fun U x => h p j hij U x
  · apply IsZero.eq_of_src
    apply HomologicalComplex.isZero_extend_X
    intro i' hi'
    change -(i' : ℤ) = i at hi'
    omega

end LateralTheory.EtaleFoundations.AwExPf
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.TateTwists.FreeExt =====

-- ===== clump member: Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyUniquenessHolds =====
-- clump-header: {"m": "Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyUniquenessHolds", "h": "module\n\npublic import Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupCochainExistsForPairing\npublic import Development.EtaleCohomology.TateTwists.FreeExt\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem LateralTheory.EtaleFoundations.etale_cup_alexanderWhitney_uniqueness_holds : LateralTheory.EtaleFoundations.EtaleAlexanderWhitneyCupCochainUnique := by
  intro R _ I J K μ E n m k hk α β γ γ' h h'
  exact LateralTheory.EtaleFoundations.AwExPf.ev_ext _ _ fun N w hw U x => (h N w hw U x).trans (h' N w hw U x).symm
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyUniquenessHolds =====

-- ===== clump member: Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupExistsOfComponents =====
-- clump-header: {"m": "Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupExistsOfComponents", "h": "module\n\npublic import Development.EtaleCohomology.TateTwists.EtaleCochainDifferentialEvaluationDegreeZero\npublic import Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupCochainExistsHolds\npublic import Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyLeibnizOfSucc\npublic import Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyLeibnizSuccHolds\npublic import Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyUniquenessHolds\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

namespace LateralTheory.Fin.EtaleCupProductNaturalInCoefficients
theorem etale_alexander_whitney_cup_leibniz_rule_of_components : LateralTheory.EtaleFoundations.EtaleAlexanderWhitneyCupLeibnizRule := by
  apply LateralTheory.EtaleFoundations.etale_cup_alexanderWhitney_leibniz_of_succ <;> first | exact _root_.LateralTheory.EtaleFoundations.etale_cup_alexanderWhitney_leibniz_succ_holds
theorem etale_cup_product_compatibility_specification_of_components : LateralTheory.EtaleFoundations.EtaleCupCompatAlexanderWhitneyCocycleSpec := by
  apply LateralTheory.EtaleFoundations.etale_cup_compat_spec_of_alexander_whitney_exists_unique_leibniz <;> first | exact _root_.LateralTheory.EtaleFoundations.etale_alexander_whitney_cup_cochain_exists_holds | exact _root_.LateralTheory.EtaleFoundations.etale_cup_alexanderWhitney_uniqueness_holds | exact etale_alexander_whitney_cup_leibniz_rule_of_components
theorem etale_cup_product_compatible_with_cochains_of_components : LateralTheory.EtaleFoundations.EtaleCupProductNaturalInCoefficients := by
  apply LateralTheory.EtaleFoundations.etale_cup_compatible_with_coefficient_maps_of_spec <;> first | exact etale_cup_product_compatibility_specification_of_components
alias intersectionNumber_baseChange := _root_.LateralTheory.Fin.EtaleCupProductNaturalInCoefficients.etale_cup_product_compatible_with_cochains_of_components
end LateralTheory.Fin.EtaleCupProductNaturalInCoefficients
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupExistsOfComponents =====
