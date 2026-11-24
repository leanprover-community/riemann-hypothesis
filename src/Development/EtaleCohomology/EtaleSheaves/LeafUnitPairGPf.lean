module

public import Development.EtaleCohomology.EtaleSheaves.LeafRingUnitPf
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
-- Members: Development.EtaleCohomology.EtaleSheaves.LeafUnitPairPf, Development.EtaleCohomology.EtaleSheaves.LeafUnitPairGPf

-- ===== clump member: Development.EtaleCohomology.EtaleSheaves.LeafUnitPairPf =====
-- clump-header: {"m": "Development.EtaleCohomology.EtaleSheaves.LeafUnitPairPf", "h": "module\n\npublic import Development.EtaleCohomology.EtaleSheaves.LeafRingUnitPf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.Modules.Sheaf\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitPairPf
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafRingUnitPf

theorem resGen_res' {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (resGen i ζ) = resGen i (ζ.map g.appTop.hom) := by
  have h1 : Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
    have h := congrArg (fun f => f.hom (Submodule.Quotient.mk (Finsupp.single ζ 1) :
        (twF q i).obj Γ(U, ⊤)))
      ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
    simp only [ModuleCat.hom_comp] at h
    refine h.symm.trans (congrArg (fun x => ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom x) ?_)
    change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.appTop.hom) (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))) = _
    rw [Finsupp.mapDomain_single]
    rfl
  unfold resGen
  rw [← h1]
  exact congrArg (fun f => f.hom (twGen i ζ)) (((resι _ (tw q i)).hom.naturality g.op)).symm

def UnitPairLoc : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ), ∃ ν : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q i)),
  ∀ (U : Scheme.{0}) (t : ℤ) (a : Sec ((res _ (tw q 0)).X 0) U) (b : Sec ((res _ (tw q i)).X t) U),
    Loc U (fun V g => ∃ ζ : Prim q Γ(V, ⊤), Sec.res g a = resGen 0 ζ) → ν.mul U 0 t t (zero_add t) a b = b

theorem sec_eq_of_loc {R : Type} [CommRing R] (F : Shv R) {U : Scheme.{0}} (x y : Sec F U)
    (h : Loc U fun V g => Sec.res g x = Sec.res g y) : x = y := by
  obtain ⟨S, hS, hP⟩ := h
  have hsh := (F.property (ModuleCat.of (ULift.{1} R) (ULift.{1} R)) S hS).isSeparatedFor
  let fx : ModuleCat.of (ULift.{1} R) (ULift.{1} R) ⟶ F.obj.obj (op U) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ x)
  let fy : ModuleCat.of (ULift.{1} R) (ULift.{1} R) ⟶ F.obj.obj (op U) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ y)
  have hxy : fx = fy := by
    refine hsh.ext (fun V g hg => ?_)
    change fx ≫ F.obj.map g.op = fy ≫ F.obj.map g.op
    refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    change (F.obj.map g.op).hom (fx.hom 1) = (F.obj.map g.op).hom (fy.hom 1)
    simpa [fx, fy] using hP V g hg
  have := congrArg (fun f => f.hom 1) hxy
  simpa [fx, fy] using this

def LeafUnitPairG : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ), ∃ ν : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q i)),
  ∀ (U : Scheme.{0}) (t : ℤ) (ζ : Prim q Γ(U, ⊤)) (b : Sec ((res _ (tw q i)).X t) U),
    ν.mul U 0 t t (zero_add t) (resGen 0 ζ) b = b

theorem unitPairLoc_of (h : LeafUnitPairG) : UnitPairLoc := by
  intro q _ i
  obtain ⟨ν, hν⟩ := h q i
  refine ⟨ν, fun U t a b ha => sec_eq_of_loc _ _ _ ?_⟩
  obtain ⟨S, hS, hP⟩ := ha
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨ζ, hζ⟩ := hP V g hg
  rw [ν.nat g 0 t t (zero_add t) a b, hζ, hν]

theorem leafUnitPair_of_loc (h : UnitPairLoc) : LeafUnitPair := by
  intro q _ i
  obtain ⟨ν, hν⟩ := h q i
  have key : ∀ k (_ : i = k), ∃ μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q k)),
      ∀ U s t w (hw : s + t = w) a b, HEq (μ.mul U s t w hw a b) (ν.mul U s t w hw a b) := by
    rintro k rfl
    exact ⟨ν, fun _ _ _ _ _ _ _ => HEq.rfl⟩
  obtain ⟨μ, hμ⟩ := key (0 + i) (zero_add i).symm
  have gen : ∀ U t w w' (h1 : 0 + t = w) (h2 : 0 + t = w') (_ : w = w') a b,
      HEq (ν.mul U 0 t w h1 a b) (ν.mul U 0 t w' h2 a b) := by
    intro U t w w' h1 h2 e a b
    subst e
    rfl
  have hgen : ∀ k (_ : k = i) (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), HEq (resGen k ζ) (resGen i ζ) := by
    rintro k rfl U ζ
    rfl
  refine ⟨μ, ?_, ?_⟩
  · intro U ζ
    have hloc : Loc U (fun V g => ∃ ζ' : Prim q Γ(V, ⊤), Sec.res g (resGen 0 ζ) = resGen 0 ζ') :=
      ⟨⊤, GrothendieckTopology.top_mem _ _, fun _ g _ => ⟨_, resGen_res' 0 g ζ⟩⟩
    exact eq_of_heq ((hμ U 0 0 0 _ _ _).trans ((heq_of_eq (hν U 0 _ _ hloc)).trans (hgen _ (zero_add i) U ζ).symm))
  · intro U t w hw a b ha
    exact (hμ U 0 t w hw a b).trans ((gen U t w t hw (zero_add t) (by omega) a b).trans (heq_of_eq (hν U t a b ha)))

theorem LeafUnitPair_of (h : LeafUnitPairG) : LeafUnitPair := leafUnitPair_of_loc (unitPairLoc_of h)

end LateralTheory.E.LeafUnitPairPf
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.EtaleSheaves.LeafUnitPairPf =====

-- ===== clump member: Development.EtaleCohomology.EtaleSheaves.LeafUnitPairGPf =====
-- clump-header: {"m": "Development.EtaleCohomology.EtaleSheaves.LeafUnitPairGPf", "h": "module\n\npublic import Development.EtaleCohomology.EtaleSheaves.LeafUnitPairPf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.Modules.Sheaf\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitPairGPf
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafRingUnitPf LateralTheory.E.LeafUnitPairPf

def IsAct (q : ℕ) (i : ℤ) (L : ∀ (U : Scheme.{0}) (t : ℤ), Sec (tw q 0) U →ₗ[ULift.{1} (ZMod q)]
    Sec ((res _ (tw q i)).X t) U →ₗ[ULift.{1} (ZMod q)] Sec ((res _ (tw q i)).X t) U) : Prop :=
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (t : ℤ) (a : Sec (tw q 0) U) (b : Sec ((res _ (tw q i)).X t) U),
      Sec.res g (L U t a b) = L V t (Sec.res g a) (Sec.res g b)) ∧
    ∀ (U : Scheme.{0}) (t : ℤ) (a : Sec (tw q 0) U) (b : Sec ((res _ (tw q i)).X t) U),
      Sec.map ((res _ (tw q i)).d t (t + 1)) (L U t a b) = L U (t + 1) a (Sec.map ((res _ (tw q i)).d t (t + 1)) b)

def LeafUnitAct : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ), ∃ L, IsAct q i L ∧
  ∀ (U : Scheme.{0}) (t : ℤ) (ζ : Prim q Γ(U, ⊤)) (b : Sec ((res _ (tw q i)).X t) U), L U t (twGen 0 ζ) b = b

def LeafPairExt : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) L, IsAct q i L →
  ∃ ν : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q i)),
    ∀ (U : Scheme.{0}) (t : ℤ) (a : Sec (tw q 0) U) (b : Sec ((res _ (tw q i)).X t) U),
      ν.mul U 0 t t (zero_add t) (Sec.map (resι _ (tw q 0)) a) b = L U t a b

theorem LeafUnitPairG_of (hact : LeafUnitAct) (hext : LeafPairExt) : LeafUnitPairG := by
  intro q _ i
  obtain ⟨L, hL, hLζ⟩ := hact q i
  obtain ⟨ν, hν⟩ := hext q i L hL
  refine ⟨ν, fun U t ζ b => ?_⟩
  exact (hν U t (twGen 0 ζ) b).trans (hLζ U t ζ b)

end LateralTheory.E.LeafUnitPairGPf
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.EtaleSheaves.LeafUnitPairGPf =====
