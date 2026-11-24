module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GammaOneGammaZeroHomogeneousCocyclesFinite
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.pair_mf :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] {r : Resid F O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B), PhiCond F.G₀ l → Finite (ResidueField B) ∧ (l : B) ∈ maximalIdeal B ∧ ∃ (h : ℕ) (χ : Fin n → F.G₀ →* (ResidueField B)ˣ), u.D.map (residue B) = GDet.ofChars χ ∧ MultFree χ h := by
  intro l _ F n O _ _ _ hc _ r B _ _ _ u hΦ
  haveI := hc.finite
  haveI := hc.char
  let e : ResidueField O ≃+* ResidueField B := RingEquiv.ofBijective _ (resMap_bijective O B)
  haveI hfin : Finite (ResidueField B) := Finite.of_equiv _ e.toEquiv
  haveI hch : CharP (ResidueField B) l := charP_of_injective_ringHom (f := e.toRingHom) e.injective l
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.1 (F.η.ker.isClosed_of_isOpen F.η_open).isCompact
  let χ : Fin n → F.G₀ →* (ResidueField B)ˣ := fun i => pushCh e.toRingHom (r.chib i)
  have hU : Function.Injective (Units.map (e.toRingHom : ResidueField O →* ResidueField B)) :=
    Units.map_injective e.injective
  have hop : ∀ i, IsOpen ((χ i).ker : Set F.G₀) := fun i => by
    have : (χ i).ker = (r.chib i).ker := MonoidHom.ker_comp_of_injective _ _ hU
    rw [this]
    exact r.chib_open i
  have hinj : Function.Injective χ := fun i j hij =>
    r.chib_inj (MonoidHom.ext fun g => hU (DFunLike.congr_fun hij g))
  obtain ⟨h, hh⟩ := exists_multFree_of_phiCond_of_injective_chars l χ hΦ hop hinj
  refine ⟨hfin, ?_, h, χ, ?_, hh⟩
  · rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ l
  · have h1 : residue B = e.toRingHom.comp (res O B : B →+* ResidueField O) :=
      RingHom.ext fun b => (e.apply_symm_apply (residue B b)).symm
    rw [h1, ← (d_gmap u.D).2.1, u.red, Resid.Dbar, (d_gmap r.Dbar).2.2.2]
    unfold GDet.ofChars
    congr 1
    refine MonoidHom.ext fun g => ?_
    change (Matrix.diagonal fun i => ((r.chib i g : (ResidueField O)ˣ) : ResidueField O)).map e.toRingHom = _
    rw [Matrix.diagonal_map (map_zero _)]
    rfl
