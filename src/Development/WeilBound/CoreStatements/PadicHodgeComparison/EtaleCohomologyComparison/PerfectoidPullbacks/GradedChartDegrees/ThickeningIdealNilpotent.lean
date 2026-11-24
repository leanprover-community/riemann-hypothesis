module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HarishChandraFormulaStatement
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationSquareOfValuationMod
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ExistsDpPow
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
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
-- Members: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GradedChartDegrees.GDSpec, Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GradedChartDegrees.ThickeningIdealNilpotent

-- ===== clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GradedChartDegrees.GDSpec =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GradedChartDegrees.GDSpec", "h": "module\n\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HarishChandraFormulaStatement\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationSquareOfValuationMod\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ExistsDpPow\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Diso

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O]

structure OL : Prop where
  tf : R.TF (S := O)
  unit : ∀ u : ℕ, ¬ l ∣ u → IsUnit (u : O)

variable {l O}

abbrev Om (l : ℕ) (O : Type) [CommRing O] (m : ℕ) : Type := O ⧸ Ideal.span {(l : O) ^ m}

abbrev Iom (l : ℕ) (O : Type) [CommRing O] (m : ℕ) : Ideal (Om l O m) := (Ideal.span {(l : O)}).map (Ideal.Quotient.mk _)

def pdm (h : OL l O) (m : ℕ) : DividedPowers (Iom l O m) := (exists_pd_l l h.unit h.tf m).choose

theorem isPdm (h : OL l O) (m : ℕ) : R.IsPd (Ideal.Quotient.mk _) (Ideal.span {(l : O)}) (pdm h m) :=
  (exists_pd_l l h.unit h.tf m).choose_spec

abbrev κm (l : ℕ) (O : Type) [CommRing O] (m : ℕ) : O →+* Om l O m ⧸ Iom l O m :=
  (Ideal.Quotient.mk _).comp (Ideal.Quotient.mk _)

abbrev Lm (h : OL l O) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (m : ℕ) : (nlBase (Om l O m) (Iom l O m) (pdm h m) l).Fun :=
  nlFun (pdm h m) l X q (κm l O m)

variable {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

abbrev lm (T : Thick (smFun X q)) (m : ℕ) : Ideal T.B := Ideal.span {(l : T.B) ^ m}

abbrev GI (T : Thick (smFun X q)) : Ideal T.B := T.J ⊔ Ideal.span {(l : T.B)}

abbrev GB (T : Thick (smFun X q)) (m : ℕ) : Type := T.B ⧸ lm (l := l) T m

abbrev GJ (T : Thick (smFun X q)) (m : ℕ) : Ideal (GB (l := l) T m) := (GI (l := l) T).map (Ideal.Quotient.mk _)

theorem lm_le (T : Thick (smFun X q)) (m : ℕ) : Ideal.span {(l : O) ^ m} ≤ (lm (l := l) T m).comap T.i := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  change T.i ((l : O) ^ m) ∈ lm (l := l) T m
  rw [map_pow, map_natCast]
  exact Ideal.mem_span_singleton_self _

def iG (T : Thick (smFun X q)) (m : ℕ) : Om l O m →+* GB (l := l) T m := Ideal.quotientMap _ T.i (lm_le T m)

def thG (T : Thick (smFun X q)) (m : ℕ) : T.B ⧸ T.J →+* GB (l := l) T m ⧸ GJ (l := l) T m :=
  Ideal.quotientMap _ (Ideal.Quotient.mk _) fun _ hx => Ideal.mem_map_of_mem _ (Ideal.mem_sup_left hx)

def Good (T : Thick (smFun X q)) (m : ℕ) : Prop :=
  R.TF (S := T.B) ∧ R.PdI (GI (l := l) T) ∧
    ∀ x ∈ GI (l := l) T, x ∈ lm (l := l) T m → ∀ j : ℕ, j ≠ 0 → ∀ y : T.B, (j.factorial : T.B) * y = x ^ j → y ∈ lm (l := l) T m

def GD (T : Thick (smFun X q)) (m : ℕ) (hT : Good (l := l) T m) : DividedPowers (GJ (l := l) T m) :=
  (RL.pd_quot hT.1 (GI (l := l) T) (lm (l := l) T m) hT.2.1 hT.2.2).choose

theorem GD_spec (T : Thick (smFun X q)) (m : ℕ) (hT : Good (l := l) T m) :
    R.IsPd (Ideal.Quotient.mk (lm (l := l) T m)) (GI (l := l) T) (GD T m hT) :=
  (RL.pd_quot hT.1 (GI (l := l) T) (lm (l := l) T m) hT.2.1 hT.2.2).choose_spec

end CrystallineSemistableComparison.Pb.Diso
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GradedChartDegrees.GDSpec =====

-- ===== clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GradedChartDegrees.ThickeningIdealNilpotent =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GradedChartDegrees.ThickeningIdealNilpotent", "h": "module\n\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GradedChartDegrees.GDSpec\nimport Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationSquareOfValuationMod\nimport Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ExistsDpPow\npublic import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Diso

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem l_mem_GI (T : Thick (smFun X q)) : ∀ x ∈ Ideal.span {(l : O)}, T.i x ∈ GI (l := l) T := by
  intro x hx
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  rw [map_mul, map_natCast]
  exact Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

theorem Iom_le (T : Thick (smFun X q)) (m : ℕ) : Iom l O m ≤ (GJ (l := l) T m).comap (iG T m) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_map]
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  exact Ideal.mem_map_of_mem _ (l_mem_GI T x hx)

def psG (T : Thick (smFun X q)) (m : ℕ) : Om l O m ⧸ Iom l O m →+* GB (l := l) T m ⧸ GJ (l := l) T m :=
  Ideal.quotientMap _ (iG T m) (Iom_le T m)

theorem ptCond (T : Thick (smFun X q)) (m : ℕ) :
    (Spec.map (CommRingCat.ofHom (thG (l := l) T m)) ≫ pt T) ≫ q =
      Spec.map (CommRingCat.ofHom ((psG T m).comp (κm l O m))) := by
  rw [Category.assoc]
  have h2 : pt T ≫ q = Spec.map (CommRingCat.ofHom (T.y.1.1.comp (Ideal.Quotient.mk ⊥))) := T.y.2
  rw [h2, ← Spec.map_comp]
  congr 1
  ext a
  change thG (l := l) T m (T.y.1.1 (Ideal.Quotient.mk ⊥ a)) = psG T m (κm l O m a)
  rw [show T.y.1.1 (Ideal.Quotient.mk ⊥ a) = Ideal.Quotient.mk T.J (T.i a) from T.w a]
  rfl

def ptG (T : Thick (smFun X q)) (m : ℕ) (h : OL l O) :
    (Lm h q m).Pt.obj (CommRingCat.of (GB (l := l) T m ⧸ GJ (l := l) T m)) :=
  ⟨(psG T m, Spec.map (CommRingCat.ofHom (thG (l := l) T m)) ≫ pt T), ptCond T m⟩

theorem thickening_ideal_nilpotent (T : Thick (smFun X q)) (m : ℕ) :
    (l ≠ 0 → IsNilpotent ((l : ℕ) : GB (l := l) T m)) ∧ (l = 0 → IsNilpotent (GJ (l := l) T m)) := by
  refine ⟨fun _ => ⟨m, ?_⟩, fun h => absurd h (Fact.out : l.Prime).ne_zero⟩
  rw [← map_natCast (Ideal.Quotient.mk (lm (l := l) T m)), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

theorem dp_G (h : OL l O) (T : Thick (smFun X q)) (m : ℕ) (hT : Good (l := l) T m) :
    IsDPMorphism (pdm h m) (GD T m hT) (iG T m) :=
  RL.pd_mor (Ideal.Quotient.mk _) (Ideal.Quotient.mk _) (Ideal.span {(l : O)}) (GI (l := l) T) (pdm h m) (GD T m hT) T.i
    (iG T m) Ideal.Quotient.mk_surjective (pdI_l l h.unit) (isPdm h m) (GD_spec T m hT) (l_mem_GI T) (fun _ => rfl)

def GObj (h : OL l O) (T : Thick (smFun X q)) (m : ℕ) (hT : Good (l := l) T m) : Thick (Lm h q m) :=
  mkT (GB (l := l) T m) (iG T m) (GJ (l := l) T m) (GD T m hT) (thickening_ideal_nilpotent T m) (dp_G h T m hT) (ptG T m h) (fun _ => rfl)

theorem lm_map {T T' : Thick (smFun X q)} (φ : T ⟶ T') (m : ℕ) : lm (l := l) T m ≤ (lm (l := l) T' m).comap φ.φ := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  change φ.φ ((l : T.B) ^ m) ∈ lm (l := l) T' m
  rw [map_pow, map_natCast]
  exact Ideal.mem_span_singleton_self _

def gφ {T T' : Thick (smFun X q)} (φ : T ⟶ T') (m : ℕ) : GB (l := l) T m →+* GB (l := l) T' m :=
  Ideal.quotientMap _ φ.φ (lm_map φ m)

theorem GI_map {T T' : Thick (smFun X q)} (φ : T ⟶ T') : ∀ x ∈ GI (l := l) T, φ.φ x ∈ GI (l := l) T' := by
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add (f := _)]
  refine add_mem (Ideal.mem_sup_left (φ.hle hy)) (Ideal.mem_sup_right ?_)
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  rw [map_mul, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem dp_gφ {T T' : Thick (smFun X q)} (φ : T ⟶ T') (m : ℕ) (hT : Good (l := l) T m) (hT' : Good (l := l) T' m) :
    IsDPMorphism (GD T m hT) (GD T' m hT') (gφ φ m) :=
  RL.pd_mor (Ideal.Quotient.mk _) (Ideal.Quotient.mk _) (GI (l := l) T) (GI (l := l) T') (GD T m hT) (GD T' m hT') φ.φ
    (gφ φ m) Ideal.Quotient.mk_surjective hT.2.1 (GD_spec T m hT) (GD_spec T' m hT') (GI_map φ) (fun _ => rfl)

theorem GJ_le {T T' : Thick (smFun X q)} (φ : T ⟶ T') (m : ℕ) : GJ (l := l) T m ≤ (GJ (l := l) T' m).comap (gφ φ m) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_map, Ideal.map_le_iff_le_comap]
  intro x hx
  exact Ideal.mem_map_of_mem _ (GI_map φ x hx)

theorem ptG_map (h : OL l O) {T T' : Thick (smFun X q)} (φ : T ⟶ T') (m : ℕ) :
    (Lm h q m).Pt.map (CommRingCat.ofHom (Ideal.quotientMap (GJ (l := l) T' m) (gφ φ m) (GJ_le φ m))) (ptG T m h) =
      ptG T' m h := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · change (Ideal.quotientMap (GJ (l := l) T' m) (gφ φ m) (GJ_le φ m)).comp (psG T m) = psG T' m
    refine Ideal.Quotient.ringHom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_))
    change Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (φ.φ (T.i a))) = Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (T'.i a))
    rw [φ.comm]
  · change Spec.map (CommRingCat.ofHom (Ideal.quotientMap (GJ (l := l) T' m) (gφ φ m) (GJ_le φ m))) ≫
        (Spec.map (CommRingCat.ofHom (thG (l := l) T m)) ≫ pt T) = Spec.map (CommRingCat.ofHom (thG (l := l) T' m)) ≫ pt T'
    rw [Site.pt_hom φ, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    ext x
    change Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (φ.φ x)) = Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (φ.φ x))
    rfl

def GMap (h : OL l O) {T T' : Thick (smFun X q)} (φ : T ⟶ T') (m : ℕ) (hT : Good (l := l) T m) (hT' : Good (l := l) T' m) :
    GObj h T m hT ⟶ GObj h T' m hT' :=
  mkH (gφ φ m) (fun r => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
      change Ideal.Quotient.mk _ (φ.φ (T.i a)) = Ideal.Quotient.mk _ (T'.i a)
      rw [φ.comm]) (dp_gφ φ m hT hT') (GJ_le φ m) (ptG_map h φ m)

def GF (h : OL l O) (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (hQ : ∀ T, Q T → Good (l := l) T m) :
    Q.FullSubcategory ⥤ Thick (Lm h q m) where
  obj T := GObj h T.obj m (hQ _ T.property)
  map φ := GMap h φ.hom m _ _
  map_id T := by
    refine CrystallineSemistableComparison.Pb.hom_ext ?_
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_)
    rfl
  map_comp φ ψ := by
    refine CrystallineSemistableComparison.Pb.hom_ext ?_
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_)
    rfl

end CrystallineSemistableComparison.Pb.Diso
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GradedChartDegrees.ThickeningIdealNilpotent =====
