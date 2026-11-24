module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlatOfFlatFibresDvr
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlatOfFormallyUnramifiedGrpEnd
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FormallyUnramifiedMulN
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RingHomFlatCodescendsAlongFaithfullyFlat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace MulEtaleDvr

variable {S : Scheme.{0}}

theorem mulN_eq_pow (G : Over S) [GrpObj G] (n : ℕ) : mulN G n = 𝟙 G ^ n := by
  rw [← MulUnramified.comp_mulN, Category.id_comp]

theorem isMonHom_mulN (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) : IsMonHom (mulN G n) := by
  constructor
  · rw [MulUnramified.comp_mulN, one_eq_one, one_pow]
  · simp only [MulUnramified.comp_mulN, MonObj.mul_eq_mul, MonObj.comp_mul,
      tensorHom_fst, tensorHom_snd, mul_pow]

theorem pullback_map_mulN {S' : Scheme.{0}} (p : S' ⟶ S) (G : Over S) [GrpObj G] (n : ℕ) :
    (Over.pullback p).map (mulN G n) = mulN ((Over.pullback p).obj G) n := by
  rw [mulN_eq_pow, mulN_eq_pow, ← (Over.pullback p).map_id]
  exact map_pow (Over.pullback p).homMonoidHom _ _

theorem isPullback_torsion (G : Over S) [GrpObj G] (n : ℕ) :
    IsPullback (torsion.ι G n).left (torsion G n).hom (mulN G n).left η[G].left := by
  have h := (IsPullback.of_hasPullback (mulN G n) (η : 𝟙_ (Over S) ⟶ G)).map (Over.forget S)
  have e : (pullback.snd (mulN G n) (η : 𝟙_ (Over S) ⟶ G)).left = (torsion G n).hom :=
    (Category.comp_id _).symm.trans (Over.w (pullback.snd (mulN G n) (η : 𝟙_ (Over S) ⟶ G)))
  exact e ▸ h

theorem isUnit_natCast_sections {R : Type} [CommRing R] {n : ℕ} (hn : IsUnit (n : R)) :
    IsUnit (n : Γ(Sp R, ⊤)) := by
  simpa using hn.map (Scheme.ΓSpecIso (.of R)).inv.hom

theorem flat_mulN_field (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (n : ℕ)
    (hn : IsUnit (n : k)) (hG : LocallyOfFiniteType G.hom) : Flat (mulN G n).left := by
  refine flat_of_flat_fieldBaseChange k (AlgebraicClosure k) (algebraMap _ _) G G _ ?_
  rw [pullback_map_mulN]
  refine flat_of_formallyUnramified_grpEnd _ _ _ ?_ (isMonHom_mulN _ n)
    (formallyUnramified_mulN _ _ n (isUnit_natCast_sections ?_))
  · exact inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom _))
  · simpa using hn.map (algebraMap k (AlgebraicClosure k))

theorem flat_pullback_mulN {T k : Type} [CommRing T] [Field k] (σ : T →+* k) (G : Over (Sp T))
    [GrpObj G] [IsCommMonObj G] (n : ℕ) (hn : IsUnit (n : T)) (hG : LocallyOfFiniteType G.hom) :
    Flat ((Over.pullback (spMap σ)).map (mulN G n)).left := by
  rw [pullback_map_mulN]
  refine flat_mulN_field k _ n (by simpa using hn.map σ) ?_
  exact inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom _))

end MulEtaleDvr


open MulEtaleDvr in
theorem etale_mulN_torsion_dvr :
    ∀ (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] (G : Over (Sp T)) [GrpObj G]
      [IsCommMonObj G] (n : ℕ), IsUnit (n : T) → Flat G.hom → LocallyOfFiniteType G.hom →
      Etale (mulN G n).left ∧ Etale (torsion G n).hom := by
  intro T _ _ _ G _ _ n hn hf hG
  have h1 : Flat (mulN G n).left :=
    flat_of_flat_fibres_dvr T (FractionRing T) G G _ hf hf hG hG
      (MulEtaleDvr.flat_pullback_mulN _ G n hn hG) (MulEtaleDvr.flat_pullback_mulN _ G n hn hG)
  have h2 := formallyUnramified_mulN _ G n (MulEtaleDvr.isUnit_natCast_sections hn)
  have h3 : LocallyOfFiniteType ((mulN G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have h4 := locallyOfFiniteType_of_comp (mulN G n).left G.hom
  have h5 : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have h6 : LocallyOfFinitePresentation (mulN G n).left := inferInstance
  have h : Etale (mulN G n).left := Etale.of_formallyUnramified_of_flat _
  exact ⟨h, MorphismProperty.of_isPullback (P := @Etale) (MulEtaleDvr.isPullback_torsion G n) h⟩

end GlobalTheory
