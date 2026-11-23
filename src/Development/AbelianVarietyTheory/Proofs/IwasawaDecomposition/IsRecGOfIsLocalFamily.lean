module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConcrete
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieTrF
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsEmbeddingOfRingTie
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsTiedOfIsRecG
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdentificationPlaceEqInducedRealPlaceStatement
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.SelfDualAtColLevel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.TrueLocal

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms GlobalTheory.Mem.LocalPack GlobalTheory.Mem.ConcreteRecord

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

def IsLocalFamily (sc : Scale) (D : D7) (L0 : LevelData D) (T : ∀ u : D.what₂.Word, Forms0 D u)
    (g : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) → GAtP (D.what₂.places.resChar w)) : Prop :=
  ∃ (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      LocId (L0 u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
        (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
        (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
    (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      Formalism.L2.Herm.awayFrom₂ (L0 u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
    (B : GL (Fin D.R.k) D.host.E)
    (iK : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      KfRec D w (nFr D (D.what₂.places.resChar w)) →+* ℂ_[D.what₂.places.resChar w])
    (lam : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w]),
    Cmp.StdB D B ∧
    (∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B) ∧
    (∀ u w hg (z : D.what₂.LL), iK u w hg (embRec D w (nFr D (D.what₂.places.resChar w)) z) =
      lamV (lam u w hg) (D.what₂.embLL z)) ∧
    (∀ u w hg, (packC D (fun u => L0 u) I ψ u w hg).posOK (iK u w hg) (lam u w hg)) ∧
    (∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      PsiTied (LL := D.what₂.LL) (O := ORec D w (nFr D (D.what₂.places.resChar w)))
        (Kf := KfRec D w (nFr D (D.what₂.places.resChar w)))
        ((T u).cls0).lev (L0 u) (D.what₂.places.resChar w) (rank_eq_first_level D.R) D.what₂.embLL
        (embRec D w (nFr D (D.what₂.places.resChar w))) (ψ u w hg)) ∧
    g = gatOf D L0 I ψ sc



theorem exists_isLocalFamily (sc : Scale) {D : D7} {L0 : LevelData D} (T : ∀ u : D.what₂.Word, Forms0 D u)
    (hS : Formalism.L2.Herm.StdTied D) (hC : Companion D L0) (hJ : ∀ u, Joint0 L0 u (T u)) (hψ : ∀ u, LevelZeroCharacterRational T u) :
    ∃ g, (∀ u w h, (g u w h).d = Module.finrank ℂ (D.mem u).A.Mu0) ∧ IsLocalFamily sc D L0 T g :=
  let I := placeId D L0 hS hC
  have hAway := GlobalTheory.Mem.AwayChar.exists_psi D L0 T hJ hψ
  let ψ := fun u w hg => Classical.choose (hAway u w hg)
  have hTied := fun u w hg => Classical.choose_spec (hAway u w hg)
  let g := gatOf D L0 I ψ sc
  have hd := gatOf_d D L0 T hJ I ψ sc
  have h : IsLocalFamily sc D L0 T g :=
    ⟨I, ψ, stdBasis D hS, embK D L0, embAlg D L0, stdBasis_std D hS, fun _ _ _ _ _ => rfl,
      embK_embAlg D L0, posOK_placeId (D := D) (L0 := L0) hS hC ψ, hTied, rfl⟩
  ⟨g, hd, h⟩



theorem isRecG_of_isLocalFamily {sc : Scale} {D : D7} {L0 : LevelData D} {T : ∀ u : D.what₂.Word, Forms0 D u}
    (hJ : ∀ u, Joint0 L0 u (T u)) (hψ : ∀ u, LevelZeroCharacterRational T u) {g} (hd : ∀ u w h, (g u w h).d = Module.finrank ℂ (D.mem u).A.Mu0)
    (h : IsLocalFamily sc D L0 T g) :
    ∃ (Gt : GatTies (setGat D g hd)) (c : LatCmp (setGat D g hd)) (G : GroupCompatibilityAll (setGat D g hd) Gt c),
      IsRecG sc (setGat D g hd) Gt c G.herm G.forms ∧ (∀ u, G.herm.lev0 u = L0 u) ∧ (∀ u, G.forms u = forms0Set D g hd (T u)) ∧
      ∀ u w hg (v : Fin ((setGat D g hd).gat u w hg).P.nV) (s : Fin (((setGat D g hd).gat u w hg).P.n' v)) (x : 𝓞 D.host.F),
        x ∈ ((G.herm.g u w hg).pl v).1.asIdeal ↔
          (0 : WithTop ℤ) < D.what₂.places.val w (tauLL (setGat D g hd) (Gt.gat_pos u w hg ⟨v, s⟩)
            (algebraMap D.host.F D.host.E (x : D.host.F))) := by
  obtain ⟨I, ψ, B, iK, lam, hBs, hB, hK, hPos, hψ', rfl⟩ := h
  exact
    let buildRec := recC D sc 1 L0 I
    -- Infer the character type from `recC` to reuse its unit instances in the constructions below.
    let ψ := (fun {A : Type} {B : A → Type 1} (_ : ∀ a, B a) (a : A) => a) buildRec ψ
    let D' := buildRec ψ hd
    let H0 : Formalism.L2.Herm.Herm0 D' := ⟨L0, levTieG D sc 1 L0 (packC D L0 I ψ) hd⟩
    have hL : ∀ u, H0.lev0 u = L0 u := fun _ => rfl
    let T' : ∀ u, Forms0 D' u := fun u => forms0Set D D'.gat D'.gat_d (T u)
    let Gt := gatTiesC D sc 1 L0 I ψ hd
    let cmp := cmpInC D sc 1 L0 I ψ hd H0 hL B hBs hB
    have CH := Test.comparison_statements D sc L0 I ψ hd H0 hL T' B hBs hB iK lam hK hPos hJ hψ hψ'
    have hpos := pos_C D sc 1 L0 I ψ hd H0 hL B hBs hB iK lam hK hPos
    have hcmp := (CH.toHyp0 hpos).toHyp
    let c := Cmp.latCmpC T' Gt cmp hcmp
    let G : GroupCompatibilityAll D' Gt c :=
      groupCompatibilityOfRecursion D sc 1 L0 I ψ hd H0 hL T' B hBs hB hcmp
        (fun u w hg => isHyperbolicAt_rec_of_placeIdentification D u w hg (I u w hg))
    have hRec : IsRecG sc D' Gt c H0 T' :=
      IsRecG.intro D L0 I ψ hd H0 hL T' B hBs hB iK lam hK hPos CH rfl
    have hRetie : IsRecG sc D' Gt c G.herm G.forms :=
      LayerTwoModel.isRecG_retie hRec G.herm.g
    have hPlace := GlobalTheory.T.mem_localPlace_asIdeal_iff_val_pos
      D sc 1 L0 I ψ hd H0 hL B hBs hB iK lam hK hPos
    ⟨Gt, c, G, hRetie, fun _ => rfl, fun _ => rfl, hPlace⟩

end GlobalTheory.Mem.Top.Bl.TrueLocal

end
