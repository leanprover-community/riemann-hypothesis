module

public import Development.EtaleCohomology.EtaleSheaves.UnitExistence
public import Development.EtaleCohomology.EtaleSheaves.LPrimLocPf
public import Development.EtaleCohomology.EtaleSheaves.LeafPrimCoverPf
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
import Mathlib.Tactic.Linter.Style
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

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.EtaleCohomology.EtaleSheaves.TwistGenerators, Development.EtaleCohomology.EtaleSheaves.TwistGenerators.LeafTwGenIndepOf, Development.EtaleCohomology.EtaleSheaves.UnitSections

-- ===== clump member: Development.EtaleCohomology.EtaleSheaves.TwistGenerators =====
-- clump-header: {"m": "Development.EtaleCohomology.EtaleSheaves.TwistGenerators", "h": "module\n\npublic import Development.EtaleCohomology.EtaleSheaves.UnitExistence\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.Modules.Sheaf\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitSecPf

def LeafTwGenIndep : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)), twGen 0 ζ = twGen 0 ξ

theorem twGen_res {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map (Scheme.Γ.map g.op).hom) := by
  unfold twGen ofRings.sec
  have h := congrArg (fun t => t.hom (Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
  simp only [ModuleCat.hom_comp] at h
  refine h.symm.trans (congrArg (fun y => ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom y) ?_)
  exact congrArg (Submodule.Quotient.mk (p := twRel q i Γ(V, ⊤))) (Finsupp.mapDomain_single (f := Prim.map (Scheme.Γ.map g.op).hom))

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (k : V ⟶ U) (x : Sec F U) :
    Sec.res h (Sec.res k x) = Sec.res (h ≫ k) x := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem res_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.res (𝟙 U) x = x := by
  show (F.obj.map (𝟙 U).op).hom x = x
  rw [op_id, F.obj.map_id]
  rfl

theorem tw_isSheafFor (q : ℕ) (U : Scheme.{0}) (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U) :
    Presieve.IsSheafFor ((tw q 0).obj ⋙ forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) S.arrows := by
  have hF := (Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology (tw q 0).obj
    (forget (ModuleCat.{1} (ULift.{1} (ZMod q))))).1 (tw q 0).property
  rw [isSheaf_iff_isSheaf_of_type] at hF
  exact hF S hS

section Glue

def cov (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) : Sieve U := Classical.choose (hP q U hU)

theorem cov_mem (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) : cov hP q U hU ∈ Scheme.etaleTopology U :=
  (Classical.choose_spec (hP q U hU)).1

theorem cov_prim (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) (V : Scheme.{0}) (g : V ⟶ U) (hg : (cov hP q U hU).arrows g) :
    Nonempty (Prim q Γ(V, ⊤)) :=
  (Classical.choose_spec (hP q U hU)).2 V g hg

def fam (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) :
    Presieve.FamilyOfElements ((tw q 0).obj ⋙ forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) (cov hP q U hU).arrows :=
  fun V g hg => twGen 0 (Classical.choice (cov_prim hP q U hU V g hg))

theorem fam_compat (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (hI : LeafTwGenIndep) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) : (fam hP q U hU).Compatible := by
  rw [Presieve.compatible_iff_sieveCompatible]
  intro Y Z f g hf
  change _ = Sec.res g (twGen 0 _)
  rw [twGen_res]
  exact hI q Z _ _

def one (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (hI : LeafTwGenIndep) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) : Sec (tw q 0) U :=
  (tw_isSheafFor q U _ (cov_mem hP q U hU)).amalgamate (fam hP q U hU) (fam_compat hP hI q U hU)

theorem one_char (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (hI : LeafTwGenIndep) (q : ℕ) [NeZero q] (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) (W : Scheme.{0}) (k : W ⟶ U) (ζ : Prim q Γ(W, ⊤)) :
    Sec.res k (one hP hI q U hU) = twGen 0 ζ := by
  refine LateralTheory.E.LeafOneSpecPf.sec_sep (ZMod q) (tw q 0) W ((cov hP q U hU).pullback k)
    (Scheme.etaleTopology.pullback_stable k (cov_mem hP q U hU)) _ _ fun V h hh => ?_
  rw [res_comp, twGen_res]
  have hv := (tw_isSheafFor q U _ (cov_mem hP q U hU)).valid_glue (fam_compat hP hI q U hU) (h ≫ k) hh
  refine hv.trans ?_
  exact hI q V _ _

end Glue

theorem LeafUnitSec_of (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (hI : LeafTwGenIndep) :
    LateralTheory.E.LeafOneExistsPf.LeafUnitSec := by
  intro q _
  refine ⟨one hP hI q, fun V U g hU hV => ?_, fun U hU ζ => ?_⟩
  · refine LateralTheory.E.LeafOneSpecPf.sec_sep (ZMod q) (tw q 0) V (cov hP q V hV) (cov_mem hP q V hV) _ _ fun W h hh => ?_
    obtain ⟨ζ⟩ := cov_prim hP q V hV W h hh
    rw [res_comp, one_char hP hI q U hU W _ ζ, one_char hP hI q V hV W h ζ]
  · rw [← one_char hP hI q U hU U (𝟙 U) ζ, res_id]

end LateralTheory.E.LeafUnitSecPf
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.EtaleSheaves.TwistGenerators =====

-- ===== clump member: Development.EtaleCohomology.EtaleSheaves.TwistGenerators.LeafTwGenIndepOf =====
-- clump-header: {"m": "Development.EtaleCohomology.EtaleSheaves.TwistGenerators.LeafTwGenIndepOf", "h": "module\n\npublic import Development.EtaleCohomology.EtaleSheaves.TwistGenerators\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.Modules.Sheaf\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitSecPf.Indep

def LeafPowLocal : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)), ∃ S : Sieve U,
  S ∈ Scheme.etaleTopology U ∧ ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g →
    ∃ a : (ZMod q)ˣ, (ξ.map (Scheme.Γ.map g.op).hom).1 = (ζ.map (Scheme.Γ.map g.op).hom).1 ^ (a : ZMod q).val

theorem twGen_pow {q : ℕ} {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    twGen 0 ξ = twGen 0 ζ := by
  unfold twGen
  congr 1
  refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, a, h, ?_⟩)
  simp
  rfl

theorem LeafTwGenIndep_of (hL : LeafPowLocal) : LeafTwGenIndep := by
  intro q _ U ζ ξ
  obtain ⟨S, hS, hSa⟩ := hL q U ζ ξ
  refine LateralTheory.E.LeafOneSpecPf.sec_sep (ZMod q) (tw q 0) U S hS _ _ fun V g hg => ?_
  obtain ⟨a, ha⟩ := hSa V g hg
  rw [twGen_res, twGen_res]
  exact (twGen_pow _ _ a ha).symm

theorem LeafUnitSec_of (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (hL : LeafPowLocal) :
    LateralTheory.E.LeafOneExistsPf.LeafUnitSec :=
  LateralTheory.E.LeafUnitSecPf.LeafUnitSec_of hP (LeafTwGenIndep_of hL)

end LateralTheory.E.LeafUnitSecPf.Indep
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.EtaleSheaves.TwistGenerators.LeafTwGenIndepOf =====

-- ===== clump member: Development.EtaleCohomology.EtaleSheaves.UnitSections =====
-- clump-header: {"m": "Development.EtaleCohomology.EtaleSheaves.UnitSections", "h": "module\n\npublic import Development.EtaleCohomology.EtaleSheaves.TwistGenerators.LeafTwGenIndepOf\npublic import Development.EtaleCohomology.EtaleSheaves.LPrimLocPf\npublic import Development.EtaleCohomology.EtaleSheaves.LeafPrimCoverPf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.Modules.Sheaf\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.UnitSections

theorem powLocal : LateralTheory.E.LeafUnitSecPf.Indep.LeafPowLocal := by
  intro q _ U ζ ξ
  obtain ⟨s, hs, hf⟩ := LateralTheory.E.L_prim_locPf.algPow q Γ(U, ⊤) ζ ξ
  obtain ⟨S, hS, hP⟩ := LateralTheory.E.L_prim_locPf.loc_of_span s hs
    (P := fun V g => ∃ a : (ZMod q)ˣ,
      (ξ.map (Scheme.Γ.map g.op).hom).1 = (ζ.map (Scheme.Γ.map g.op).hom).1 ^ (a : ZMod q).val) (by
      intro f hfs V g hu
      obtain ⟨a, n, hn⟩ := hf f hfs
      refine ⟨a, ?_⟩
      have h := LateralTheory.E.L_prim_locPf.eq_of_unit_kill g.appTop.hom hn hu
      rw [map_pow] at h
      exact h)
  exact ⟨S, hS, hP⟩

theorem LeafUnitSec_of : LateralTheory.E.LeafOneExistsPf.LeafUnitSec :=
  LateralTheory.E.LeafUnitSecPf.Indep.LeafUnitSec_of _root_.LateralTheory.E.LeafPrimCoverPf.leafPrimCover_pf powLocal

end LateralTheory.E.UnitSections
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.EtaleSheaves.UnitSections =====
