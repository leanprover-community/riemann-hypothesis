module

public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseLevel
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Dimension
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseLocal
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseFixed
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseInputs
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseInv
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BijectiveGsCompactZmodDualityMap
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Finite
import GroundTheory.ProfiniteCohomology.RestrictedRamification.FiniteOpen
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section Local

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)
  [NeZero n] (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
include hnS



theorem bijective_gsRootsLocalMor_of_places (v : S) : Function.Bijective (gsRootsLocalMor S ιs n v).hom :=
  (exists_isPrimitiveRoot_maxUnramifiedOutside K S n (NeZero.ne n) hnS).elim fun _ hz =>
    Additive.ofMul.bijective.comp ((bijective_rootsOfUnityMapHom n
      ((ιs v).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom hz).comp Additive.toMul.bijective)

theorem bijective_gsLocalInvRoots_of_places (v : S) : Function.Bijective (gsLocalInvRoots S ιs n v) := by
  have e : ⇑(gsLocalInvRoots S ιs n v) =
      (localDualityHypotheses (Ksep := AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
        (natCast_ne_zero_adicCompletion S n v)).tTop ∘ (cohomologyMap (gsRootsLocalMor S ιs n v) 2).hom :=
    funext (gsLocalInvRoots_eq S ιs n v)
  rw [e]
  exact (bijective_localDualityHypotheses_tTop S n v).comp
    (bijective_cohomologyMap_of_bijective _ (bijective_gsRootsLocalMor_of_places S ιs n hnS v) 2)

end Local

section P1

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)
  [NeZero n] (hodd : Odd n ∨ IsTotallyComplex K.1) (h3 : Subsingleton (cohomology (gsRoots S n) 3))

def GsPairingNondegenerate : Prop :=
  (∀ x : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1,
      (∀ y : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2,
        gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs) (zmodMulPairingRight n (gsRoots S n)
          (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) y x) = 0) → x = 0) ∧
    (∀ y : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2,
      (∀ x : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1,
        gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs) (zmodMulPairingRight n (gsRoots S n)
          (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) y x) = 0) → y = 0)

end P1

section Level

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  (n ℓ k : ℕ) [NeZero n] (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hodd : Odd n ∨ IsTotallyComplex K.1) (h3 : Subsingleton (cohomology (gsRoots S n) 3))

def GsPairingInput (n ℓ : ℕ) [NeZero n] : Prop :=
  ∀ (L : FiniteSubfield) (S' : Set (HeightOneSpectrum (𝓞 L.1))) [Fintype S']
    (ιs' : ∀ v : S', ℚ̄ →ₐ[L.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 L.1)).adicCompletion L.1)),
    (∀ v : HeightOneSpectrum (𝓞 L.1), ((ℓ : ℕ) : 𝓞 L.1) ∈ v.asIdeal → v ∈ S') →
    (∀ ζ : ℚ̄, ζ ^ n = 1 → ζ ∈ L.1) → ∀ (hodd' : Odd n ∨ IsTotallyComplex L.1)
    (h3' : Subsingleton (cohomology (gsRoots S' n) 3)), GsPairingNondegenerate S' ιs' n hodd' h3'


omit [Fintype S] [NeZero n] in
include hnk hS in
theorem natCast_not_mem_of_not_mem : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal :=
  fun v hv h => hv (mem_of_natCast_pow_mem S n ℓ k hnk hS v h)


include hℓ hnk hS in
private theorem gsLevelBijective_of_pairing [Nonempty S] (hμ : ∀ ζ : ℚ̄, ζ ^ n = 1 → ζ ∈ K.1)
    (hP : GsPairingNondegenerate S ιs n hodd h3) :
    GsLevelBijective (S := S) (ιs := ιs) (n := n) (gsCompactInv S ιs n hodd h3) := by
  refine ⟨bijective_gsCompactInv_of_mem S n ιs ℓ k hℓ hnk hS hμ hodd h3, ?_⟩
  intro r s h
  have h3Z := subsingleton_zmodRep_gs_three S n ℓ k hnk hS hodd
  have hfin1 := finite_zmodRep_gs_one S n ℓ k hnk hS
  have hfin2 := finite_gsRoots_compact_two S n ℓ k hnk hS ιs
  have hleft := hP.1
  have hright := hP.2
  have hdual := bijective_gs_compactZmodDualityMap S ιs n ℓ k hℓ hnk hS hμ
    hodd h3 h3Z hfin1 hfin2
  -- The kernel checks the conversion of the pairing hypotheses and the duality map.
  run_tac Lean.Elab.Tactic.withMainContext do
    let dual ← Lean.Meta.getFVarFromUserName `hdual
    let args ← #[`hleft, `hright, `r, `s, `h].mapM (m := Lean.MetaM) Lean.Meta.getFVarFromUserName
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.assign (Lean.Meta.mkExpectedPropHint (Lean.mkAppN dual args) (← goal.getType))


include hℓ hnk hS in
theorem gsBaseBijective_of_le (hP : GsPairingInput n ℓ)
    (hcores : ∀ U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S),
      Function.Surjective (compactCores (gsFinFamily S ιs) U (gsRoots S n) 3).hom)
    (W₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (hW₀ : ∀ σ ∈ W₀, ∀ ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ, ζ ^ n = 1 →
      σ (ζ : maxUnramifiedOutside K.1 ℚ̄ S) = ζ)
    {L : FiniteSubfield} [Fact (K ≤ L)] (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hUW : gsOpenSubgroup S hL ≤ W₀) :
    GsBaseBijective S ιs n (gsOpenSubgroup S hL) (gsCompactInv S ιs n hodd h3) := by
  have hnS := natCast_not_mem_of_not_mem S n ℓ k hnk hS
  have : Nonempty S := nonempty_of_natCast_mem S ℓ hℓ hS
  let SL := placesOver (F := K.1) (L := L.1) S
  let ιsL := gsMackeyEmbeddings (F := K.1) (L := L.1) (Ω := ℚ̄) hL ιs
  let : Fintype SL := fintypePlacesOver (L := L) S
  have : Nonempty SL := nonempty_placesOver_of_natCast_mem (L := L) S hℓ hS
  have hSL : ∀ w : HeightOneSpectrum (𝓞 L.1), ((ℓ : ℕ) : 𝓞 L.1) ∈ w.asIdeal → w ∈ SL :=
    fun w hw => mem_placesOver_of_natCast_mem hS hw
  have hμL : ∀ ζ : ℚ̄, ζ ^ n = 1 → ζ ∈ L.1 :=
    rootsOfUnity_mem_of_gsOpenSubgroup_le (L := L) S n hL W₀ hW₀ hUW (NeZero.ne n) hnS
  have hoddL : Odd n ∨ IsTotallyComplex L.1 := hodd.imp id fun h => by
    have := h
    exact isTotallyComplex_of_algebra K.1 L.1
  have h3L := subsingleton_gsRoots_three (K := L) SL n ℓ k hnk hSL hoddL
  have hPL := hP L SL ιsL hSL hμL hoddL h3L
  let U := gsOpenSubgroup (F := K.1) (L := L.1) (Ω := ℚ̄) S hL
  have hInv := surjective_gsCompactInv S n ιs hodd h3 fun v =>
    (bijective_gsLocalInvRoots_of_places S ιs n hnS v).2
  have hsurj : GsCoresSurjective S ιs n U (gsCompactInv S ιs n hodd h3) := by
    have hcomp := hInv.comp (hcores U)
    -- The kernel identifies the underlying function with the bundled composition.
    run_tac Lean.Elab.Tactic.withMainContext do
      let proof ← Lean.Meta.getFVarFromUserName `hcomp
      let goal ← Lean.Elab.Tactic.getMainGoal
      goal.assign (Lean.Meta.mkExpectedPropHint proof (← goal.getType))
  have hLev := gsLevelBijective_of_pairing (K := L) SL ιsL n ℓ k hℓ hnk hSL hoddL h3L hμL hPL
  intro r s h
  exact bijective_zmodCompactDualityMap_gsOpenSubgroup (K := K) (L := L) S ιs hL n (gsCompactInv S ιs n hodd h3)
    (gsCompactInv (K := L) SL ιsL n hoddL h3L) hLev hsurj (r := r) (s := s) h

end Level

end

end GroundTheory.ProfCoh
