import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTripleAtOfConj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHypothesesOfAttached
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.FrobDualOfTripleAttN
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Triple
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlIsTripleWithcharpolyFrob

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.TripleGal
theorem noInv_all_places_alt (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i)
    (hT : ∃ AI, Nonempty (LocTied (D.ntw.l i) (D.loc (D.ntw.l i)) AI)) (h2 : ValuationStabilityAtRing D.ntw i s)
    (hA : _root_.GlobalTheory.TripleGal.TripleAttN D.naut bkP i s) (hJ : NoJump bkP i s) (v : HeightOneSpectrum (𝓞 D.host.E)) :
    NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v := by
  by_cases hl : v ∈ placesOver D.host.E (D.ntw.l i)
  · exact ⟨GlobalTheory.T.noDecompositionInvariants_aboveL_of_noHodgeJump D bkP i s hJ v hl, GlobalTheory.T.noInv_tateDual_of_hodge_of_noJump D bkP i s hT (_root_.GlobalTheory.TripleGal.HodgeOfAtt.hodgeL_of_tripleAtt_n D bkP i s hA) hJ v hl⟩
  by_cases hS : v ∈ Spl (X := D.ntw) i
  · rcases hS.1 with hg | hp
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hg
      exact GlobalTheory.T.noInv_at_type_primes D i s h2 k (fun e => hl (e ▸ hk)) v hk
    · exact GlobalTheory.T.noDecompositionInvariants_auxiliaryPrime D i s (_root_.GlobalTheory.TripleUnramified.unrRho_of_tripleAtt_n D bkP i s hA) v (Finset.mem_coe.1 hp)
  · obtain ⟨ι, hι⟩ := _root_.GlobalTheory.TripleGal.pure_of_tripleAtt_n D bkP i s hA
    exact _root_.GlobalTheory.PurityInvariants.noInv_of_pure_n D i s ι hι v hl hS
theorem adm1_adm8_selfDual_noJump_of_tripleAttN : ∀ (D : D7) (bkP : BlochKatoReduction.BK D), GlobalTheory.TypeLeaf.FrobDense D → (∀ i, D.ntw.NonzeroIndexPlace i → (∃ AI, Nonempty (LocTied (D.ntw.l i) (D.loc (D.ntw.l i)) AI))) → BlochKatoReduction.adm2 D → (∀ i, D.ntw.NonzeroIndexPlace i → ∀ s, _root_.GlobalTheory.TripleGal.TripleAttN D.naut bkP i s) → BlochKatoReduction.adm1 bkP ∧ BlochKatoReduction.adm8 D ∧ ∀ i, D.ntw.NonzeroIndexPlace i → True ∧ ∀ s : D.ntw.Sig i, SelfDual i s ∧ NoJump bkP i s := by
  intro D bkP hF hT h2 hA
  have hJ : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ s, NoJump bkP i s := fun i hi s => by
    obtain ⟨ι, J, h, h'⟩ := _root_.GlobalTheory.TripleGal.Jumps.exists_jumpsAre_goodJ_n D bkP i s (hA i hi s)
    exact GlobalTheory.T.noHodgeJump_of_goodJumpMultiset D bkP i s ι J (_root_.GlobalTheory.TripleGal.HodgeOfAtt.hodgeL_of_tripleAtt_n D bkP i s (hA i hi s)) h h'
  refine ⟨fun i hi s => ?_, fun i hi s => ?_, fun i hi => ⟨trivial, fun s => ⟨?_, hJ i hi s⟩⟩⟩
  · obtain ⟨ι, J, h, h'⟩ := _root_.GlobalTheory.TripleGal.Jumps.exists_jumpsAre_goodJ_n D bkP i s (hA i hi s)
    exact GlobalTheory.T.isotypicValuationAtRing_of_unrRho_hodgeL_noInv_negCount D bkP i s (_root_.GlobalTheory.TripleUnramified.unrRho_of_tripleAtt_n D bkP i s (hA i hi s)) (_root_.GlobalTheory.TripleGal.HodgeOfAtt.hodgeL_of_tripleAtt_n D bkP i s (hA i hi s))
      (_root_.GlobalTheory.TripleGal.noInv_all_places_alt D bkP i s (hT i hi) (h2 i hi s) (hA i hi s) (hJ i hi s))
      (GlobalTheory.T.conjugateNegativeJumpCount_of_goodHodgeJumps D bkP i s ι J (_root_.GlobalTheory.TripleGal.HodgeOfAtt.hodgeL_of_tripleAtt_n D bkP i s (hA i hi s)) h h')
  · exact GlobalTheory.T.characterTwistExists_of_unrRho_of_hkFrob D i s (_root_.GlobalTheory.TripleUnramified.unrRho_of_tripleAtt_n D bkP i s (hA i hi s)) (_root_.GlobalTheory.TripleGal.HkFrobProof.hkFrob_of_tripleAtt_n D bkP i s (hA i hi s))
  · exact GlobalTheory.T.selfDual_lattice_of_conjDualCharpoly D i s (h2 i hi s) (GlobalTheory.T.conjDualCharpoly_of_splitFrobenius_dense D hF i s (_root_.GlobalTheory.TripleFrobDual.frobDual_of_tripleAtt_n D bkP i s (hA i hi s)))
end GlobalTheory.TripleGal
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open Formalism.L2.Host Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.HeightCounting (CharSide)
open GlobalTheory.GalOfCusp GlobalTheory.TripleGal GlobalTheory.Triple
open GlobalTheory.TypeLeaf (FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary (embOver)
open GlobalTheory.JumpDictionaryFoundation (exists_embOver embOver_true_apply)
section Twist
variable {D : D7} {C₀ : CharFrame D} (S : CharSide D C₀) {n : ℕ} (π : D.naut.CG n) {ξ : HChar D.host.E} (hξ : ξ.IsUnitary)
variable {π}
end Twist
section Chars
variable {D : D7} (C : CharFrame D) (l : ℕ) (j : Fin D.R.m)
end Chars
section Triple
variable {D : D7} {T : WDTie D.nd D.naut} {C₀ C : CharFrame D} (S : CharSide D C₀)
  {art : Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om} {i : D.ntw.Tw} {s : D.ntw.Sig i}
  {ρ : Reading D.ntw i (D.ntw.side i s)} {σ : D.what₂.FT} {π : D.naut.CG D.R.r}
  {r : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* GL (Fin D.R.r) (Qbar (D.ntw.l i))} {ν : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* (D.ntw.O0 i)ˣ}
  {w : D.what₂.places.Pl} {red : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.Zbar (D.ntw.l i) →+* FbAt D w}
theorem frobMatch_rhoS_of_isTripleWith (ha : GlobalTheory.HeckeGal.IsGlobalArtin art) (h : _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red) :
    FrobMatch D (twBy S π C.isEta.unitary.inv) (rd i (ρ.ι.toRingHom.comp ρ.κ)) (D.ntw.rhoS i s)
      (-((D.R.t : ℝ) / 2) + (1 - (D.R.r : ℝ)) / 2) := by
  filter_upwards [(D.ntw.S0 i).finite_toSet.compl_mem_cofinite] with P hP B g hB hg
  obtain ⟨h1, h2⟩ := twBy_unr S C.isEta.unitary.inv (h.unr_of_notMem hP) (C.isEta.unr P).inv
  refine (h.charpoly_frob ha (fun hl => hP (D.ntw.twistExcludedPlaces_contains_residueChar i hl)) (fun k hk => hP (D.ntw.placesOver_subset_exceptional i k hk)) hB hg).trans ?_
  rw [D.naut.frobEig_tw _ _ h1, h2, Multiset.map_map, Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun a _ => ?_)
  simp only [Function.comp_apply]
  rw [shiftChar_val, cpow_add_real, Complex.ofReal_neg, Complex.cpow_neg, HChar.val_inv, Units.val_inv_eq_inv_val]
  congr 2
  rw [mul_inv]
  ring
end Triple
end GlobalTheory.TripleLocal
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open Formalism.L2.Host Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.HeightCounting (CharSide)
open GlobalTheory.GalOfCusp GlobalTheory.TripleGal GlobalTheory.Triple
open GlobalTheory.TypeLeaf (FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary (embOver)
open GlobalTheory.JumpDictionaryFoundation (exists_embOver embOver_true_apply)
section Twist
variable {D : D7} {C₀ : CharFrame D} (S : CharSide D C₀) {n : ℕ} (π : D.naut.CG n) {ξ : HChar D.host.E} (hξ : ξ.IsUnitary)
variable {π}
end Twist
section Chars
variable {D : D7} (C : CharFrame D) (l : ℕ) (j : Fin D.R.m)
end Chars
section Triple
variable {D : D7} {T : WDTie D.nd D.naut} {C₀ C : CharFrame D} (S : CharSide D C₀)
  {art : Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om} {i : D.ntw.Tw} {s : D.ntw.Sig i}
  {ρ : Reading D.ntw i (D.ntw.side i s)} {σ : D.what₂.FT} {π : D.naut.CG D.R.r}
  {r : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* GL (Fin D.R.r) (Qbar (D.ntw.l i))} {ν : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* (D.ntw.O0 i)ˣ}
  {w : D.what₂.places.Pl} {red : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.Zbar (D.ntw.l i) →+* FbAt D w}
theorem frobMatch_Tgl_of_isTripleWith (ha : GlobalTheory.HeckeGal.IsGlobalArtin art) (hχ : IsChars C art ρ) (h : _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red) :
    FrobMatch D (twBy S π (mu_unitary C (D.ntw.l i) (jIdx s))) (rd i (ρ.ι.toRingHom.comp ρ.κ)) (Tgl i s)
      (((D.R.r : ℝ) / 2 + -((D.R.t : ℝ) / 2)) + (1 - (D.R.r : ℝ)) / 2) := by
  filter_upwards [(D.ntw.S0 i).finite_toSet.compl_mem_cofinite] with P hP B g hB hg
  have hl : P ∉ placesOver D.host.E (D.ntw.l i) := fun hl => hP (D.ntw.twistExcludedPlaces_contains_residueChar i hl)
  have hk : ∀ k, P ∉ placesOver D.host.E (D.host.g k) := fun k hk => hP (D.ntw.placesOver_subset_exceptional i k hk)
  have hμ := mu_unr C (jIdx s) hk fun hp => hP (D.ntw.primes_subset_exceptional i hp)
  obtain ⟨h1, h2⟩ := twBy_unr S (mu_unitary C (D.ntw.l i) (jIdx s)) (h.unr_of_notMem hP) hμ.inv
  obtain ⟨n, hn⟩ := hχ.chiS
  have h3 := hn.frob ha (Or.inl hl) (fun x hx => by
    rw [blockChar, GlobalTheory.GalChar.block_loc (C.isEta.unr P) hx]; exact hμ x hx) hB hg
  have h4 := h.charpoly_frob ha hl hk hB hg
  rw [← Matrix.charpoly_map] at h4
  have h5 : (Tmat i s g).map ρ.toC = (((blockChar C (D.ntw.l i) (jIdx s)).val P : ℂˣ) : ℂ) •
      ((D.ntw.rhoS i s g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)).map ρ.toC := by
    ext x y
    simp only [Tmat, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_units_inv]
    rw [ρ.toC_apply ((chiS i s g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i), h3, inv_inv]
  have h6 := charpoly_smul_of_prod _ (((D.naut.frobEig (D.naut.locG π P)).map fun a =>
    a * ((normV P : ℕ) : ℂ) ^ (((1 - (D.R.r : ℝ)) / 2 : ℝ) : ℂ) * (((shiftChar C).val P : ℂˣ) : ℂ)⁻¹))
    (((blockChar C (D.ntw.l i) (jIdx s)).val P : ℂˣ) : ℂ) (by rw [h4, Multiset.map_map]; rfl)
  rw [← h5, Matrix.charpoly_map] at h6
  rw [Tgl_coe]
  refine h6.trans ?_
  rw [D.naut.frobEig_tw _ _ h1, h2, Multiset.map_map, Multiset.map_map, Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun a _ => ?_)
  simp only [Function.comp_apply]
  rw [shiftChar_val, blockChar_val, cpow_add_real, cpow_add_real, Complex.ofReal_neg, Complex.cpow_neg, HChar.val_inv,
    Units.val_inv_eq_inv_val]
  congr 2
  have := (C.eta.val P).ne_zero
  have := cpow_ne_zero' P (((D.R.t : ℝ) / 2 : ℝ) : ℂ)
  field_simp
end Triple
end GlobalTheory.TripleLocal
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open Formalism.L2.Host Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.HeightCounting (CharSide)
open GlobalTheory.GalOfCusp GlobalTheory.TripleGal GlobalTheory.Triple
open GlobalTheory.TypeLeaf (FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary (embOver)
open GlobalTheory.JumpDictionaryFoundation (exists_embOver embOver_true_apply)
section Twist
variable {D : D7} {C₀ : CharFrame D} (S : CharSide D C₀) {n : ℕ} (π : D.naut.CG n) {ξ : HChar D.host.E} (hξ : ξ.IsUnitary)
variable {π}
end Twist
section Chars
variable {D : D7} (C : CharFrame D) (l : ℕ) (j : Fin D.R.m)
end Chars
section Triple
variable {D : D7} {T : WDTie D.nd D.naut} {C₀ C : CharFrame D} (S : CharSide D C₀)
  {art : Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om} {i : D.ntw.Tw} {s : D.ntw.Sig i}
  {ρ : Reading D.ntw i (D.ntw.side i s)} {σ : D.what₂.FT} {π : D.naut.CG D.R.r}
  {r : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* GL (Fin D.R.r) (Qbar (D.ntw.l i))} {ν : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* (D.ntw.O0 i)ˣ}
  {w : D.what₂.places.Pl} {red : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.Zbar (D.ntw.l i) →+* FbAt D w}
theorem hkSat_of_isTripleWith (h : _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red) :
    HkSat D.naut i s (ρ.ι.toRingHom.comp ρ.κ) (twBy S π (mu_unitary C (D.ntw.l i) (jIdx s))) := by
  intro P hP hs k hk
  obtain ⟨x, h1, h2⟩ := h.hecke k P hk hs hP
  refine ⟨x, h1.symm, h2.trans ?_⟩
  have hμ := mu_unr C (jIdx s) (fun k hk => hP (D.ntw.placesOver_subset_exceptional i k hk)) fun hp => hP (D.ntw.primes_subset_exceptional i hp)
  rw [(twBy_unr S (mu_unitary C (D.ntw.l i) (jIdx s)) (h.unr_of_notMem hP) hμ.inv).2, heckeVal, satake, Multiset.map_map]
  have e1 : ((k : ℂ) * ((D.R.r : ℂ) - k)) / 2 = ((k * (D.R.r - k) / 2 : ℕ) : ℂ) := by
    have := congrArg (Nat.cast : ℕ → ℂ) (two_mul_half D.R hk)
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hk] at this
    rw [← this]
    push_cast
    ring
  have e2 : -((D.R.r : ℂ) + D.R.t) / 2 = -((D.R.nV / 2 : ℕ) : ℂ) := by
    have := congrArg (Nat.cast : ℕ → ℂ) (two_mul_nV_half D.R)
    rw [Nat.cast_mul, Nat.cast_add] at this
    rw [← this]
    push_cast
    ring
  rw [e1, e2, Complex.cpow_neg, Complex.cpow_natCast, Complex.cpow_natCast]
  congr 2
  refine Multiset.map_congr rfl fun a _ => ?_
  simp [mul_comm]
end Triple
end GlobalTheory.TripleLocal
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.GalS
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.TripleLocal
end UpperTheory.GalS
namespace GlobalTheory.TripleResidual
open NumberField IsDedekindDomain Polynomial Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.TameLabels GlobalTheory.AntiRamConj GlobalTheory.TwistDet
open GlobalTheory.TypeLeaf (WildOne FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (OnW IsBaseChange IsGaloisRepOf IsReduction Zbar GaloisReps GalE toFb)
open scoped Pointwise
variable {D : D7} (Y : NTw D.R D.host D.what₂ D.LL0 D.nd)
end GlobalTheory.TripleResidual
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleLocal GlobalTheory.TypeLeaf
namespace GlobalTheory.TripleLocal
end GlobalTheory.TripleLocal
namespace GlobalTheory.GoodRowMono
variable {D : D7}
end GlobalTheory.GoodRowMono
end
namespace GlobalTheory.TripleLocal
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleGal
open GlobalTheory.TypeLeaf (FrobDense)
variable {D : D7} {T : WDTie D.nd D.naut} {i : D.ntw.Tw} {j : FractionRing (D.ntw.O0 i) →+* ℂ}
  {ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.ntw.O0 i)} {π : D.naut.CG D.R.r} {s : ℝ}
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open Formalism.L2.Host Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.HeightCounting (CharSide)
open GlobalTheory.GalOfCusp GlobalTheory.TripleGal GlobalTheory.Triple
open GlobalTheory.TypeLeaf (FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary (embOver)
open GlobalTheory.JumpDictionaryFoundation (exists_embOver embOver_true_apply)
variable {D : D7} {T : WDTie D.nd D.naut} {C₀ C : CharFrame D} (S : CharSide D C₀)
  {art : Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om} {i : D.ntw.Tw} {s : D.ntw.Sig i}
  {ρ : Reading D.ntw i (D.ntw.side i s)} {σ : D.what₂.FT} {π : D.naut.CG D.R.r}
  {r : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* GL (Fin D.R.r) (Qbar (D.ntw.l i))} {ν : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* (D.ntw.O0 i)ˣ}
  {w : D.what₂.places.Pl} {red : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.Zbar (D.ntw.l i) →+* FbAt D w}
theorem triple_att_n_of_is_triple_with (hF : FrobDense D) (hG : UpperTheory.GalS.GalHodgeN D T) (ha : GlobalTheory.HeckeGal.IsGlobalArtin art)
    (hχ : IsChars C art ρ) (h : _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red) (S : CharSide D C₀) :
    TripleAttN D.naut (bk0 D) i s := by
  have hsep := fun k w hk => GlobalTheory.GoodRowMono.sep_over_g hG h.good h.param.csd h.param.lab k (w := w) hk
  have hthr : ∀ k w, w ∈ placesOver D.host.E (D.host.g k) → UpperTheory.GalS.thr w D.R.r = 2 := fun k w hk =>
    UpperTheory.GalS.thr_split (D.host.g_prime k) hk (D.nd.g_split k)
      (DiscreteGroups.sglob.DzType.big_of_le_nV D k (by unfold Ranks.nV; omega))
  have hR := rowFacts (C := C) (i := i) S h.param (fun v => by
    by_cases hv : ∀ k, v ∉ placesOver D.host.E (D.host.g k)
    · exact D.naut.unr_mono0 _ (h.param.unr v hv)
    · push Not at hv
      obtain ⟨k, hk⟩ := hv
      exact (UpperTheory.GalS.nc_of_sep T (by rw [D.naut.locG_dim]; exact hthr k v hk) (hsep k v hk)).2.1) (jIdx s)
  have htw : ∀ {ξ : HChar D.host.E} (hξ : ξ.IsUnitary) k v, v ∈ placesOver D.host.E (D.host.g k) → ξ.TameAt v →
      UpperTheory.GalS.Nc D.nd D.naut (D.naut.locG (twBy S π hξ) v) := fun hξ k v hk ht => by
    rw [twBy, D.naut.locG_tw]
    exact UpperTheory.GalS.nc_of_sep T (by rw [D.naut.lpDim_char _ _ (D.naut.locG_dim _ _), D.naut.locG_dim]; exact hthr k v hk)
      (UpperTheory.GalS.sep_char (GlobalTheory.RowTieLP.main D T) (D.naut.locG_dim _ _)
      (hG.2.2.2 _ S _ v (by rwa [rankOneCuspidal_unitaryChar_equiv_apply_symm])) (UpperTheory.GalS.inePol_coeff_zero T _) (hsep k v hk))
  have tinv : ∀ {ξ : HChar D.host.E} v, ξ.TameAt v → ξ⁻¹.TameAt v := fun v ht x h1 h2 => by
    rw [Formalism.L2.Host.HChar.loc_inv, ht x h1 h2, inv_one]
  have n1 : ∀ v ∈ placesOver D.host.E (D.ntw.l i),
      UpperTheory.GalS.Nc D.nd D.naut (D.naut.locG (twBy S π C.isEta.unitary.inv) v) := fun v _ => by
    by_cases hv : ∀ k, v ∉ placesOver D.host.E (D.host.g k)
    · exact .of_unr (hR.unr₁ v hv)
    · push Not at hv
      obtain ⟨k, hk⟩ := hv
      exact htw _ k v hk (tinv v fun x h1 _ => C.isEta.unr v x h1)
  have n2 : ∀ v ∈ placesOver D.host.E (D.ntw.l i),
      UpperTheory.GalS.Nc D.nd D.naut (D.naut.locG (twBy S π (mu_unitary C (D.ntw.l i) (jIdx s))) v) := fun v hl => by
    by_cases hv : ∀ k, v ∉ placesOver D.host.E (D.host.g k)
    · exact .of_unr (hR.unr v hv (by simpa using GlobalTheory.TripleGal.HodgeOfAtt.not_mem_pD D i hl))
    · push Not at hv
      obtain ⟨k, hk⟩ := hv
      exact htw _ k v hk (tinv v (GlobalTheory.MuTameQS.tameAt_mul ((C.isMu0 _).tame v) ((isDelta_delAt C _).tame v)))
  have hφ := (GlobalTheory.GalChar.isEmbedding_toQ (D.ntw.twistBaseCoefficientRing_isAdic i) ρ.κ_alg).continuous
  have hne : ∀ u : (D.ntw.O0 i)ˣ, GlobalTheory.GalChar.toQ ρ.κ u ≠ 0 := fun u => (u.isUnit.map _).ne_zero
  have s1 : IsSSRep (mapRep (GlobalTheory.GalChar.toQ ρ.κ) (D.ntw.rhoS i s)) := isSSRep_of_smul _ (fun g => hne (ν g)) h.rho (_root_.UpperTheory.GalS.galW' h.gal).2.1
  have s2 : IsSSRep (mapRep (GlobalTheory.GalChar.toQ ρ.κ) (Tgl i s)) :=
    isSSRep_of_smul _ (fun g => hne (chiS i s g)⁻¹) (fun g => by
      change ((Tgl i s g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)).map _ = _
      rw [Tgl_coe]
      ext x y
      exact map_mul (GlobalTheory.GalChar.toQ ρ.κ) _ _) s1
  have c2 : Continuous fun g => (Tgl i s g : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)) := by
    simp only [Tgl_coe, Tmat]
    exact (Units.continuous_coe_inv.comp (GlobalTheory.GalChar.continuous_units _ (D.ntw.twistCharacterFamily_continuous i _ _))).smul (D.ntw.rhoS_cont i s)
  obtain ⟨c, hc⟩ := GlobalTheory.GalChar.odd_r D.R
  obtain ⟨d, hd⟩ := D.R.t_odd
  have a1 := attN_of_isSSRep_mapRep_of_nc_locG hF hG (twBy_csd S _ h.param.csd (isCSD_inv (GlobalTheory.EtaSelfDual.isCSD_of_isEtaT _ _ _ C.isEta)))
    (twBy_regAlg S _ h.param.ralg (eta_inf C) fun g =>
      ⟨⟨-d - 1, by rw [hd]; push_cast; ring⟩, -d, by rw [hd]; push_cast; ring⟩)
    (D.ntw.rhoS_cont i s) (_root_.GlobalTheory.TripleLocal.frobMatch_rhoS_of_isTripleWith S ha h) hφ ρ.κ_alg (fun _ => rfl) s1 n1
  have a2 := attN_of_isSSRep_mapRep_of_nc_locG hF hG hR.csd
    (twBy_regAlg S _ h.param.ralg (mu_inf C _ (jIdx s)) fun g => by
      obtain ⟨z, hz⟩ := eExp_int (jIdx s) g
      exact ⟨⟨z + c - d, by rw [hz, hc, hd]; push_cast; ring⟩, -z + c - d, by rw [hz, hc, hd]; push_cast; ring⟩)
    c2 (_root_.GlobalTheory.TripleLocal.frobMatch_Tgl_of_isTripleWith S ha hχ h) hφ ρ.κ_alg (fun _ => rfl) s2 n2
  refine ⟨_, _, _, ?_, ?_, hR, _root_.GlobalTheory.TripleLocal.hkSat_of_isTripleWith S h⟩
  · convert a1 using 1
    ring
  · convert a2 using 1
    ring
end
end GlobalTheory.TripleLocal
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open Formalism.L2.Host Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.HeightCounting (CharSide)
open GlobalTheory.GalOfCusp GlobalTheory.TripleGal GlobalTheory.Triple
open GlobalTheory.TypeLeaf (FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary (embOver)
open GlobalTheory.JumpDictionaryFoundation (exists_embOver embOver_true_apply)
section Twist
variable {D : D7} {C₀ : CharFrame D} (S : CharSide D C₀) {n : ℕ} (π : D.naut.CG n) {ξ : HChar D.host.E} (hξ : ξ.IsUnitary)
variable {π}
end Twist
section Chars
variable {D : D7} (C : CharFrame D) (l : ℕ) (j : Fin D.R.m)
end Chars
section Triple
variable {D : D7} {T : WDTie D.nd D.naut} {C₀ C : CharFrame D} (S : CharSide D C₀)
  {art : Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om} {i : D.ntw.Tw} {s : D.ntw.Sig i}
  {ρ : Reading D.ntw i (D.ntw.side i s)} {σ : D.what₂.FT} {π : D.naut.CG D.R.r}
  {r : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* GL (Fin D.R.r) (Qbar (D.ntw.l i))} {ν : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* (D.ntw.O0 i)ˣ}
  {w : D.what₂.places.Pl} {red : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.Zbar (D.ntw.l i) →+* FbAt D w}
end Triple
theorem triple_att_n_of_is_triple {D : D7} {T : WDTie D.nd D.naut} {C₀ : CharFrame D} (S : CharSide D C₀) (hF : FrobDense D)
    (hG : _root_.UpperTheory.GalS.GalHodgeN D T) (h : _root_.GlobalTheory.Triple.IsGaloisTriple D) (i : D.ntw.Tw) (hi : D.ntw.NonzeroIndexPlace i) (s : D.ntw.Sig i) :
    _root_.GlobalTheory.TripleGal.TripleAttN D.naut (bk0 D) i s := by
  obtain ⟨C, art, h⟩ := h
  obtain ⟨ρ, h1, σ, π, r, ν, w, red, h2⟩ := h.triple hi s
  exact _root_.GlobalTheory.TripleLocal.triple_att_n_of_is_triple_with hF hG h.artin h1 h2 S
end GlobalTheory.TripleLocal
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open Formalism.L2.Host Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.HeightCounting (CharSide)
open GlobalTheory.GalOfCusp GlobalTheory.TripleGal GlobalTheory.Triple
open GlobalTheory.TypeLeaf (FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary (embOver)
open GlobalTheory.JumpDictionaryFoundation (exists_embOver embOver_true_apply)
section Twist
variable {D : D7} {C₀ : CharFrame D} (S : CharSide D C₀) {n : ℕ} (π : D.naut.CG n) {ξ : HChar D.host.E} (hξ : ξ.IsUnitary)
variable {π}
end Twist
section Chars
variable {D : D7} (C : CharFrame D) (l : ℕ) (j : Fin D.R.m)
end Chars
section Triple
variable {D : D7} {T : WDTie D.nd D.naut} {C₀ C : CharFrame D} (S : CharSide D C₀)
  {art : Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om} {i : D.ntw.Tw} {s : D.ntw.Sig i}
  {ρ : Reading D.ntw i (D.ntw.side i s)} {σ : D.what₂.FT} {π : D.naut.CG D.R.r}
  {r : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* GL (Fin D.R.r) (Qbar (D.ntw.l i))} {ν : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* (D.ntw.O0 i)ˣ}
  {w : D.what₂.places.Pl} {red : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.Zbar (D.ntw.l i) →+* FbAt D w}
end Triple
theorem adm1_adm8_selfDual_noJump_of_isTriple {D : D7} {T : WDTie D.nd D.naut} {C₀ : CharFrame D} (S : CharSide D C₀)
    (hF : FrobDense D) (hG : _root_.UpperTheory.GalS.GalHodgeN D T) (h2 : BlochKatoReduction.adm2 D) (h : _root_.GlobalTheory.Triple.IsGaloisTriple D) :
    BlochKatoReduction.adm1 (bk0 D) ∧ BlochKatoReduction.adm8 D ∧
      ∀ i, D.ntw.NonzeroIndexPlace i → True ∧ ∀ s : D.ntw.Sig i, SelfDual i s ∧ NoJump (bk0 D) i s :=
  _root_.GlobalTheory.TripleGal.adm1_adm8_selfDual_noJump_of_tripleAttN D (bk0 D) hF (fun _ _ => ⟨_, ⟨D.locT _⟩⟩) h2 (_root_.GlobalTheory.TripleLocal.triple_att_n_of_is_triple S hF hG h)
end GlobalTheory.TripleLocal
end
end
end
