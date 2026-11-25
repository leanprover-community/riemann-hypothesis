module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ToContinuousLinearMapMemHomIn
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRestrictedProdFinAwayIffIsProdMeasureFinAway
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Mult MeasureTheory IsDedekindDomain
open NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Mem.Th
open Formalism.MainNotions.KudlaSiegelWeil (Restr)
open GlobalTheory.PRep (smoothPart smoothRep IsSmooth IsAdmissible fixed)
open GlobalTheory.Orb (dsRep TypeDataG)
open scoped TensorProduct ComplexConjugate InnerProductSpace

namespace GlobalTheory.AutMult

section Vectors

variable {G X H : Type} [Group G] [AddCommGroup X] [Module ℂ X] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def kFinVec (ρ : Representation ℂ G X) (K : Subgroup G) : Submodule ℂ X where
  carrier := {x | ∃ W : Submodule ℂ X, FiniteDimensional ℂ W ∧ ∀ k ∈ K, ρ k x ∈ W}
  zero_mem' := ⟨⊥, inferInstance, fun k _ => by simp⟩
  add_mem' := fun ⟨W, _, h⟩ ⟨W', _, h'⟩ =>
    ⟨W ⊔ W', inferInstance, fun k hk => by rw [map_add (f := _)]; exact Submodule.add_mem_sup (h k hk) (h' k hk)⟩
  smul_mem' := fun c _ ⟨W, hW, h⟩ => ⟨W, hW, fun k hk => by rw [map_smul]; exact W.smul_mem c (h k hk)⟩

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem isSmooth_smoothRep (ρ : Representation ℂ G X) : IsSmooth (smoothRep ρ) := fun v => by
  have : {g : G | smoothRep ρ g v = v} = {g : G | ρ g v = v} := Set.ext fun _ => Subtype.ext_iff
  exact this ▸ v.2

abbrev smRep (π : G →* (H →L[ℂ] H)) : Representation ℂ G (smoothPart (toRep π)) := smoothRep (toRep π)

end Vectors

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def GPl : Formalism.MainNotions.SchurIrreducible.Pl F → Type
  | .inl w => GArch σ J w
  | .inr v => GLoc σ J v

instance : ∀ v, Group (GPl σ J v)
  | .inl w => inferInstanceAs (Group (GArch σ J w))
  | .inr v => inferInstanceAs (Group (GLoc σ J v))

instance : ∀ v, TopologicalSpace (GPl σ J v)
  | .inl w => inferInstanceAs (TopologicalSpace (GArch σ J w))
  | .inr v => inferInstanceAs (TopologicalSpace (GLoc σ J v))

def projPl : ∀ v, GAd σ J →* GPl σ J v
  | .inl w => projArch σ J w
  | .inr v => proj σ J v

def embPl : ∀ v, GPl σ J v →* GAd σ J
  | .inl w => embArch σ J w
  | .inr v => emb σ J v

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def HasCompPl (v : Formalism.MainNotions.SchurIrreducible.Pl F) {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (δ : GPl σ J v →* (X →L[ℂ] X)) (π : GAd σ J →* (H →L[ℂ] H)) : Prop := IsIsotypic δ (π.comp (embPl σ J v))

variable {Hs : Formalism.MainNotions.SchurIrreducible.Pl F → Type} [∀ v, NormedAddCommGroup (Hs v)] [∀ v, InnerProductSpace ℂ (Hs v)]

abbrev IsFactorisation (δ : ∀ v, GPl σ J v →* (Hs v →L[ℂ] Hs v)) (ξ : ∀ v, Hs v) (π : GAd σ J →* (H →L[ℂ] H))
    (B : (∀ v, Hs v) → H) : Prop := IsRestrTensor (projPl σ J) δ ξ π B

variable {σ J} {δ : ∀ v, GPl σ J v →* (Hs v →L[ℂ] Hs v)} {ξ : ∀ v, Hs v} {π : GAd σ J →* (H →L[ℂ] H)}
  {B : (∀ v, Hs v) → H}

end Places

variable {D : D7} (V : HSp D)

section Groups

abbrev Gv (v : HeightOneSpectrum (𝓞 D.host.F)) : Type := GLoc D.sp.cm.sig V.gram v

abbrev Gw (w : InfinitePlace D.host.F) : Type := GArch D.sp.cm.sig V.gram w

abbrev Kv (v : HeightOneSpectrum (𝓞 D.host.F)) : Subgroup (Gv V v) := stabLoc D.sp.cm.sig V.gram (frameLat V) v

abbrev embV (v : HeightOneSpectrum (𝓞 D.host.F)) : Gv V v →* GA D V := emb D.sp.cm.sig V.gram v

abbrev embW (w : InfinitePlace D.host.F) : Gw V w →* GA D V := embArch D.sp.cm.sig V.gram w

def locFin (v : HeightOneSpectrum (𝓞 D.host.F)) : Gv V v →* GfC V :=
  (embV V v).codRestrict _ fun x => mem_finPts.2 (projInf_emb _ _ v x)

def finLoc (v : HeightOneSpectrum (𝓞 D.host.F)) : GfC V →* Gv V v := (proj D.sp.cm.sig V.gram v).comp (GfC V).subtype

def archInf (w : InfinitePlace D.host.F) : Gw V w →* GinfC V :=
  (embW V w).codRestrict _ fun x => mem_infPts.2 (projFin_embArch _ _ w x)

def infArch (w : InfinitePlace D.host.F) : GinfC V →* Gw V w := (projArch D.sp.cm.sig V.gram w).comp (GinfC V).subtype

def toFin : GA D V →* GfC V :=
  ((ofFin D.sp.cm.sig V.gram).comp (projFin _ _)).codRestrict _ fun _ => mem_finPts.2 (projInf_ofFin _ _ _)

def toInf : GA D V →* GinfC V :=
  ((ofInf D.sp.cm.sig V.gram).comp (projInf _ _)).codRestrict _ fun _ => mem_infPts.2 (projFin_ofInf _ _ _)

def KOff (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Subgroup (GfC V) :=
  (levelOff D.sp.cm.sig V.gram (frameLat V) S).subgroupOf (GfC V)

variable {V}

@[simp] theorem coe_locFin (v : HeightOneSpectrum (𝓞 D.host.F)) (x : Gv V v) : (locFin V v x : GA D V) = embV V v x := rfl

theorem toInf_mul_toFin (g : GA D V) : (toInf V g : GA D V) * toFin V g = g := ofInf_projInf_mul_ofFin_projFin _ _ g

theorem commute_inf_fin (x : GinfC V) (y : GfC V) : Commute (x : GA D V) y :=
  ext_inf_fin _ _ (by simp [mem_finPts.1 y.2]) (by simp [mem_infPts.1 x.2])

@[simp] theorem toFin_coe (y : GfC V) : toFin V y = y := (finPtsEquiv D.sp.cm.sig V.gram).apply_symm_apply y

@[simp] theorem toFin_coe_inf (x : GinfC V) : toFin V x = 1 :=
  Subtype.ext ((congrArg (ofFin _ _) (mem_infPts.1 x.2)).trans (map_one _))

@[simp] theorem toInf_coe_fin (y : GfC V) : toInf V y = 1 :=
  Subtype.ext ((congrArg (ofInf _ _) (mem_finPts.1 y.2)).trans (map_one _))

@[simp] theorem toInf_coe (x : GinfC V) : toInf V x = x :=
  Subtype.ext (by simpa using toInf_mul_toFin (x : GA D V))

variable (V)

theorem continuous_toFin : Continuous (toFin V) := ((continuous_ofFin _ _).comp (continuous_projFin _ _)).subtype_mk _

theorem continuous_toInf : Continuous (toInf V) := ((continuous_ofInf _ _).comp (continuous_projInf _ _)).subtype_mk _

end Groups

variable {H X W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup X] [InnerProductSpace ℂ X]
  [AddCommGroup W] [Module ℂ W] {S : D.what₂.Tau → SPar}

section Components

def HasArchComp (w : InfinitePlace D.host.F) (δ : Gw V w →* (X →L[ℂ] X)) (π : GA D V →* (H →L[ℂ] H)) : Prop :=
  IsIsotypic δ (π.comp (embW V w))

def FinHasLocComp {Y : Type} [AddCommGroup Y] [Module ℂ Y] (v : HeightOneSpectrum (𝓞 D.host.F))
    (σv : Representation ℂ (Gv V v) Y) (σ : Representation ℂ (GfC V) W) : Prop := IsIsotypicAlg σv (σ.comp (locFin V v))

abbrev IsFinFactorisation {N : HeightOneSpectrum (𝓞 D.host.F) → Type} [∀ v, AddCommGroup (N v)] [∀ v, Module ℂ (N v)]
    (σs : ∀ v, Representation ℂ (Gv V v) (N v)) (s : ∀ v, N v) (σ : Representation ℂ (GfC V) W) : Prop :=
  IsRestrTensorAlg (finLoc V) σs s σ

variable {V}

theorem isIrrUnitary_dsRep (M : DSModel V S) (τ : D.what₂.Tau) : IsIrrUnitary (dsRep M τ) :=
  ⟨(M.ds τ).1, Orb.isUnitaryRep_dsRep M τ, Orb.isTopIrreducible_dsRep M τ⟩

def HasDSComp (M : DSModel V S) (π : GA D V →* (H →L[ℂ] H)) : Prop := ∀ τ, HasArchComp V (placeOf D τ) (dsRep M τ) π

def IsDSTensor (M : DSModel V S) (δ : GinfC V →* (X →L[ℂ] X)) : Prop :=
  ∃ B, IsRestrTensor (fun τ => infArch V (placeOf D τ)) (dsRep M) 0 δ B

open Classical in
def homDS (M : DSModel V S) (ρ : GA D V →* (H →L[ℂ] H)) (U : Submodule ℂ H) :
    Submodule ℂ (ContinuousMultilinearMap ℂ M.H H) := homPi (fun τ => embW V (placeOf D τ)) (dsRep M) ρ U

open Classical in
def homFinDS (σ : Representation ℂ (GfC V) W) (M : DSModel V S) (ρ : GA D V →* (H →L[ℂ] H)) (U : Submodule ℂ H) :
    Submodule ℂ (W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H H) :=
  homTensorPi (GfC V).subtype (fun τ => embW V (placeOf D τ)) σ (dsRep M) ρ U

open Classical in
def IsCopyFinDS (σ : Representation ℂ (GfC V) W) (M : DSModel V S) (ρ : GA D V →* (H →L[ℂ] H)) (U : Submodule ℂ H) :
    Prop := IsTensorCopyPi (GfC V).subtype (fun τ => embW V (placeOf D τ)) σ (dsRep M) ρ U

open Classical in
theorem mem_homDS {θ : InfF D} (hθ : IsInfFam θ) {M : DSModel V S} {ρ : GA D V →* (H →L[ℂ] H)} {U : Submodule ℂ H}
    {Φ : ContinuousMultilinearMap ℂ M.H H} : Φ ∈ homDS M ρ U ↔ (∀ y, Φ y ∈ U) ∧ ∀ τ,
      ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y, Φ (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (Φ y) := by
  refine and_congr_right fun _ => forall_congr' fun τ => ⟨fun h g hg y => ?_, fun h x y => ?_⟩
  · obtain ⟨x, rfl⟩ := exists_archEquiv_eq V (embOverOf D τ) rfl hg
    rw [atTau_archEquiv hθ V _ rfl]
    exact h x y
  · exact atTau_archEquiv hθ V (embOverOf D τ) rfl x ▸ h _ (archEquiv_mem_UH V (embOverOf D τ) rfl x) y

variable {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] {πf : GfC V →* (Y →L[ℂ] Y)}
  {πi : GinfC V →* (X →L[ℂ] X)} {π ρ : GA D V →* (H →L[ℂ] H)} {U : Submodule ℂ H}

def finPart (δ : GinfC V →* (X →L[ℂ] X)) (hU : IsSubrep ρ U) :
    Representation ℂ (GfC V) (homIn δ (ρ.comp (GinfC V).subtype) U) :=
  PRep.sub (postRep X (ρ.comp (GfC V).subtype)) _ fun g T hT => ⟨fun x => hU.2 g _ (hT.1 x), fun k x =>
    (congrArg (ρ g) (hT.2 k x)).trans (DFunLike.congr_fun (((commute_inf_fin k g).map ρ).eq.symm) (T x))⟩

abbrev finPartSm (δ : GinfC V →* (X →L[ℂ] X)) (hU : IsSubrep ρ U) :
    Representation ℂ (GfC V) (smoothPart (finPart δ hU)) := smoothRep (finPart δ hU)

def finPartDS (M : DSModel V S) (hU : IsSubrep ρ U) : Representation ℂ (GfC V) (homDS M ρ U) :=
  PRep.sub (postRepPi M.H (ρ.comp (GfC V).subtype)) _ fun g T hT => ⟨fun x => hU.2 g _ (hT.1 x), fun τ k x =>
    (congrArg (ρ g) (hT.2 τ k x)).trans
      (DFunLike.congr_fun (((commute_inf_fin (archInf V _ k) g).map ρ).eq.symm) (T x))⟩

abbrev finPartDSSm (M : DSModel V S) (hU : IsSubrep ρ U) : Representation ℂ (GfC V) (smoothPart (finPartDS M hU)) :=
  smoothRep (finPartDS M hU)

abbrev finRes (π : GA D V →* (H →L[ℂ] H)) : Representation ℂ (GfC V) H := toRep (π.comp (GfC V).subtype)

end Components

end GlobalTheory.AutMult

end
