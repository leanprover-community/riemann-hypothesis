import Formalism.LocalToGlobal.Columns.TiedRec
import Formalism.LocalToGlobal.HermitianColumns.ColsHerm
import Formalism.LocalToGlobal.HermitianForms.FormsTied
import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel

section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Col.CH

open Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LevelData (D : ColRec) :=
  letI := D.host.cmStar
  ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)

structure HermCols (D : ColRec) where

  lev0 : LevelData D

  lev : ∀ (u : D.what₂.Word) (i : ℕ), 1 ≤ i → i ≤ D.R.m →
    StepLevel D.sp.cm (D.sp.X i) D.host.g (D.mem u).A.T D.R.f

  cls : ∀ (u : D.what₂.Word) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m),
    ClassTie D.sp.cm (D.sp.X i) (lev u i h1 hm).Lb (lev u i h1 hm).U ((D.mem u).C.stab i) (D.clsLat u i)

  vT : ∀ u : D.what₂.Word, (D.mem u).A.vT ≃
    {v : HeightOneSpectrum (𝓞 D.host.F) // (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal}

  Fv : ∀ (u : D.what₂.Word) (v : (D.mem u).A.vT), (D.mem u).A.Fv v ≃+* (𝓞 D.host.F ⧸ (vT u v).1.asIdeal)

section Abbr

variable (D : ColRec) (u : D.what₂.Word)

abbrev Ld (i : ℕ) (c : (D.mem u).C.cls i) : Submodule (𝓞 D.host.E) (D.sp.X i).V :=
  Formalism.HermitianLatticesTheory.dual (D.sp.X i).hT (D.clsLat u i c)

abbrev GX (i : ℕ) : Subgroup ((D.sp.X i).V ≃ₗ[D.host.E] (D.sp.X i).V) := Formalism.HermitianLatticesTheory.isom (D.sp.X i).hT

abbrev Lk (P : Ideal (𝓞 D.host.E)) (i : ℕ) (c : (D.mem u).C.cls i) : Submodule (𝓞 D.host.E) (D.sp.X i).V :=
  D.clsLat u i c ⊔ P • Ld D u i c

end Abbr

set_option maxHeartbeats 4000000 in

structure AtT (D : ColRec) (u : D.what₂.Word)
    (e : (D.mem u).A.vT ≃ {v : HeightOneSpectrum (𝓞 D.host.F) // (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal})
    (eF : ∀ v : (D.mem u).A.vT, (D.mem u).A.Fv v ≃+* (𝓞 D.host.F ⧸ (e v).1.asIdeal)) where

  piU : 𝓞 D.host.E
  piU_K : (piU : D.host.E) ∈ D.host.K
  piU_norm : (piU : D.host.E) * D.host.conj (piU : D.host.E) = ((D.mem u).A.T : D.host.E)
  piU_cong : (piU - 1) ∈ Ideal.span
    {((D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) : 𝓞 D.host.E)}

  Pv : (D.mem u).A.vT → Ideal (𝓞 D.host.E)
  Pv_max : ∀ v, (Pv v).IsMaximal
  Pv_pi : ∀ v, piU ∈ Pv v
  Pv_over : ∀ v, (Pv v).comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = (e v).1.asIdeal

  res : ∀ v, 𝓞 D.host.E →+* (D.mem u).A.Fv v
  res_surj : ∀ v, Function.Surjective (res v)
  res_ker : ∀ v, RingHom.ker (res v) = Pv v
  res_F : ∀ v (a : 𝓞 D.host.F), eF v (res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a)) = Ideal.Quotient.mk _ a

  seen : ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T →
    ∀ (v : (D.mem u).A.vT) (x : 𝓞 D.host.E) (y : D.what₂.LL),
      D.what₂.embLL y = D.host.emb (D.eTau ((D.fm u).tauOf w v)).1 (x : D.host.E) →
      ((0 : WithTop ℤ) < D.what₂.places.val w y ↔
        x ∈ (if (D.fm u).seenP w then Pv v else Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) (Pv v)))

  disc : ∀ i, i ≤ D.R.m → ∀ c : (D.mem u).C.cls i,
    Nonempty ((Ld D u i c ⧸ (D.clsLat u i c).comap (Ld D u i c).subtype) ≃ₗ[𝓞 D.host.E]
      (𝓞 D.host.E ⧸ Ideal.span {(((D.mem u).A.T : ℕ) : 𝓞 D.host.E)}))

  pr : ∀ i v (c : (D.mem u).C.cls i), Ld D u i c →+ (D.fm u).lv i v c
  pr_surj : ∀ i, i ≤ D.R.m → ∀ v c, Function.Surjective (pr i v c)
  pr_smul : ∀ i v c (a : 𝓞 D.host.E) (y : Ld D u i c), pr i v c (a • y) = res v a • pr i v c y
  pr_ker : ∀ i, i ≤ D.R.m → ∀ v c (y : Ld D u i c), pr i v c y = 0 ↔ (y : (D.sp.X i).V) ∈ Pv v • Ld D u i c

  fv_ker : ∀ i, i ≤ D.R.m → ∀ v c (y : Ld D u i c),
    (D.fm u).fv i v c (pr i v c y) = 0 ↔ (y : (D.sp.X i).V) ∈ Lk D u (Pv v) i c

  prk : ∀ i v (c : (D.mem u).C.cls i), Lk D u (Pv v) i c →+ (D.fm u).lk i v c
  prk_surj : ∀ i, i ≤ D.R.m → ∀ v c, Function.Surjective (prk i v c)
  prk_smul : ∀ i v c (a : 𝓞 D.host.E) (y : Lk D u (Pv v) i c), prk i v c (a • y) = res v a • prk i v c y
  prk_ker : ∀ i, i ≤ D.R.m → ∀ v c (y : Lk D u (Pv v) i c),
    prk i v c y = 0 ↔ (y : (D.sp.X i).V) ∈ Pv v • Lk D u (Pv v) i c

  te_tie : ∀ i, i ≤ D.R.m → ∀ v c (y : Ld D u i c), (D.fm u).fv i v c (pr i v c y) = 1 →
    ∀ h : ((D.mem u).A.T : D.host.E) • (y : (D.sp.X i).V) ∈ Lk D u (Pv v) i c,
      prk i v c ⟨_, h⟩ = (D.fm u).te i v c

  upG : ∀ i v (c : (D.mem u).C.cls i), Ld D u i c → GX D i

  up_tie : ∀ i, i ≤ D.R.m → ∀ v c (y : Ld D u i c), (D.fm u).fv i v c (pr i v c y) = 1 →
    haveI := (Pv_max v).isPrime
    SameOff (Pv v) (Formalism.HermitianLatticesTheory.gmap (upG i v c y).1 (D.clsLat u i ((D.fm u).up i v c (pr i v c y)))) (D.clsLat u i c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (Pv v) (Formalism.HermitianLatticesTheory.gmap (upG i v c y).1 (D.clsLat u i ((D.fm u).up i v c (pr i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (Pv v) (Ld D u i c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (Pv v) (Formalism.HermitianLatticesTheory.gmap (upG i v c y).1 (Ld D u i ((D.fm u).up i v c (pr i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (Pv v) (Ld D u i c ⊔
          Submodule.span (𝓞 D.host.E) {((D.mem u).A.T : D.host.E)⁻¹ • (y : (D.sp.X i).V)}) ∧
      (∀ (z : Ld D u i ((D.fm u).up i v c (pr i v c y)))
        (hz : ((D.mem u).A.T : D.host.E) • (upG i v c y).1 (z : (D.sp.X i).V) ∈ Ld D u i c),
        (D.fm u).fv i v _ (pr i v _ z) = (D.fm u).fv i v c (pr i v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : Ld D u i ((D.fm u).up i v c (pr i v c y)))
        (hz : (upG i v c y).1 (z : (D.sp.X i).V) ∈ Ld D u i c),
        (D.fm u).fv i v' _ (pr i v' _ z) = (D.fm u).fv i v' c (pr i v' c ⟨_, hz⟩))
  dnG : ∀ i v (c : (D.mem u).C.cls i), Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c) → GX D i

  dn_tie : ∀ i, i ≤ D.R.m → ∀ v c (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)), g ≠ 0 →
    haveI := (Pv_max v).isPrime
    SameOff (Pv v) (Formalism.HermitianLatticesTheory.gmap (dnG i v c g).1 (D.clsLat u i ((D.fm u).dn i v c g))) (D.clsLat u i c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (Pv v) (Formalism.HermitianLatticesTheory.gmap (dnG i v c g).1 (Ld D u i ((D.fm u).dn i v c g))) =
        Formalism.HermitianLatticesTheory.localization₂ (Pv v) (D.clsLat u i c) ∧
      (∀ (z : Ld D u i ((D.fm u).dn i v c g)) (hz : (dnG i v c g).1 (z : (D.sp.X i).V) ∈ Lk D u (Pv v) i c),
        (D.fm u).fv i v _ (pr i v _ z) = g (prk i v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : Ld D u i ((D.fm u).dn i v c g)) (hz : (dnG i v c g).1 (z : (D.sp.X i).V) ∈ Ld D u i c),
        (D.fm u).fv i v' _ (pr i v' _ z) = (D.fm u).fv i v' c (pr i v' c ⟨_, hz⟩))
  dilG : ∀ i v, ((D.mem u).A.Fv v)ˣ → (D.mem u).C.cls i → GX D i

  dil_tie : ∀ i, i ≤ D.R.m → ∀ v (a : ((D.mem u).A.Fv v)ˣ) c,
      Formalism.HermitianLatticesTheory.gmap (dilG i v a c).1 (D.clsLat u i ((D.fm u).dil i v a c)) = D.clsLat u i c ∧
      (∀ (z : Ld D u i ((D.fm u).dil i v a c)) (hz : (dilG i v a c).1 (z : (D.sp.X i).V) ∈ Ld D u i c),
        (D.fm u).fv i v _ (pr i v _ z) = (a : (D.mem u).A.Fv v) * (D.fm u).fv i v c (pr i v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : Ld D u i ((D.fm u).dil i v a c)) (hz : (dilG i v a c).1 (z : (D.sp.X i).V) ∈ Ld D u i c),
        (D.fm u).fv i v' _ (pr i v' _ z) = (D.fm u).fv i v' c (pr i v' c ⟨_, hz⟩))

  lattice₂ : (D.fm u).clsP → Submodule (𝓞 D.host.E) D.sp.X'.V

  levP : StepLevel0 D.sp.cm D.sp.X' D.host.g (crdLat D.sp.X' D.sp.X'.L0)

  clsP : ClassTie D.sp.cm D.sp.X' (crdLat D.sp.X' D.sp.X'.L0) levP.U (D.fm u).stabilizer₂ lattice₂

  z0 : (D.sp.X D.R.m).V
  cocycle_zero_mem_invariants : z0 ∈ Submodule.span D.host.E {D.sp.z}
  hermitianForm_lastCoordinateUniformizerVector_self : (D.sp.X D.R.m).hT z0 z0 = ((D.mem u).A.T : D.host.E)
  tilG : (D.fm u).clsP → GX D D.R.m

  til_tie : ∀ c : (D.fm u).clsP,
    Formalism.HermitianLatticesTheory.gmap (tilG c).1 (D.clsLat u D.R.m ((D.fm u).til c)) =
      (lattice₂ c).map (D.sp.iX'.restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {z0} ∧
    ∀ v (z : Ld D u D.R.m ((D.fm u).til c)) (a : 𝓞 D.host.E),
      (a : D.host.E) = (D.sp.X D.R.m).hT z0 ((tilG c).1 (z : (D.sp.X D.R.m).V)) →
      (D.fm u).fv D.R.m v _ (pr D.R.m v _ z) = res v a

def Lev0Tied (D : ColRec) (H : HermCols D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Type :=
  ∀ u, ColLevelX (H.lev0 u) (fun x => x ∈ D.host.K) (aT u).piU (H.vT u)
    (fun v c z => (D.fm u).fv 0 v c ((aT u).pr 0 v c z))

def Ad0 (D : ColRec) (H : HermCols D) (u : D.what₂.Word) (c c' : (D.mem u).C.cls 0) (γ : GX D 0)
    (v : (D.mem u).A.vT) : Prop :=
  AdStep D.sp.cm.sig D.sp.gram0 (H.lev0 u).U ((H.lev0 u).y c) ((H.lev0 u).y c')
    (toGLb ((D.sp.X 0).frame.reindex (finCongr D.sp.rank0)) γ.1) (H.vT u v).1

def AdI (D : ColRec) (H : HermCols D) (u : D.what₂.Word) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m)
    (c c' : (D.mem u).C.cls i) (γ : GX D i) (v : (D.mem u).A.vT) : Prop :=
  AdStep D.sp.cm.sig (D.sp.X i).gram (H.lev u i h1 hm).U ((H.cls u i h1 hm).y c) ((H.cls u i h1 hm).y c')
    (toGLb (D.sp.X i).frame γ.1) (H.vT u v).1

structure AdTied (D : ColRec) (H : HermCols D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Prop where
  up0 : ∀ u v c (y : Ld D u 0 c), (D.fm u).fv 0 v c ((aT u).pr 0 v c y) = 1 →
    Ad0 D H u c ((D.fm u).up 0 v c ((aT u).pr 0 v c y)) ((aT u).upG 0 v c y) v
  upI : ∀ u i h1 hm v c (y : Ld D u i c), (D.fm u).fv i v c ((aT u).pr i v c y) = 1 →
    AdI D H u i h1 hm c ((D.fm u).up i v c ((aT u).pr i v c y)) ((aT u).upG i v c y) v
  dn0 : ∀ u v c g, g ≠ 0 → Ad0 D H u c ((D.fm u).dn 0 v c g) ((aT u).dnG 0 v c g) v
  dnI : ∀ u i h1 hm v c g, g ≠ 0 → AdI D H u i h1 hm c ((D.fm u).dn i v c g) ((aT u).dnG i v c g) v
  dil0 : ∀ u v a c, Ad0 D H u c ((D.fm u).dil 0 v a c) ((aT u).dilG 0 v a c) v
  dilI : ∀ u i h1 hm v a c, AdI D H u i h1 hm c ((D.fm u).dil i v a c) ((aT u).dilG i v a c) v

def CofTied (D : ColRec) (H : HermCols D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Prop :=
  ∀ u, D.cOf u * ((aT u).piU : D.host.E) = ((aT D.u₀).piU : D.host.E)

def PiGConst (D : ColRec) (H : HermCols D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) (X : Lev0Tied D H aT) : Prop :=
  ∀ u u', (X u).piG = (X u').piG

def stabPLin (D : ColRec) (H : HermCols D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) (u : D.what₂.Word)
    (c : (D.fm u).clsP) (s : (D.fm u).stabilizer₂ c) : D.sp.X'.V ≃ₗ[D.host.E] D.sp.X'.V :=
  (toGLb D.sp.X'.frame).symm ((aT u).clsP.stabI c s : GL (Fin D.sp.X'.rank) D.host.E)

def stabMLin (D : ColRec) (H : HermCols D) (u : D.what₂.Word) (h1 : 1 ≤ D.R.m)
    (c : (D.mem u).C.cls D.R.m) (s : (D.mem u).C.stab D.R.m c) :
    (D.sp.X D.R.m).V ≃ₗ[D.host.E] (D.sp.X D.R.m).V :=
  (toGLb (D.sp.X D.R.m).frame).symm
    ((H.cls u D.R.m h1 le_rfl).stabI c s : GL (Fin (D.sp.X D.R.m).rank) D.host.E)

def StabMapTied (D : ColRec) (H : HermCols D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Prop :=
  ∀ (u : D.what₂.Word) (h1 : 1 ≤ D.R.m) (c : (D.fm u).clsP) (s : (D.fm u).stabilizer₂ c),
    (∀ x : D.sp.X'.V,
      ((aT u).tilG c).1 (stabMLin D H u h1 _ ((D.fm u).stabMap c s) (((aT u).tilG c).1.symm (D.sp.iX' x))) =
        D.sp.iX' (stabPLin D H aT u c s x)) ∧
    ((aT u).tilG c).1 (stabMLin D H u h1 _ ((D.fm u).stabMap c s) (((aT u).tilG c).1.symm (aT u).z0)) = (aT u).z0

def FvStepTied (D : ColRec) (H : HermCols D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Type :=
  ∀ (u : D.what₂.Word) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (v : (D.mem u).A.vT),
    FvTie D.sp.cm (D.sp.X i) (H.lev u i h1 hm).Lb (H.cls u i h1 hm).y (D.clsLat u i) (H.vT u v).1
      ((D.mem u).A.Fv v) (fun c z => (D.fm u).fv i v c ((aT u).pr i v c z))

def StdTied (D : ColRec) : Prop :=
  (∀ i, i ≤ D.R.m → IsStd (D.sp.X i)) ∧ IsStd D.sp.X'

def BaseTied (D : ColRec) (H : HermCols D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Prop :=
  ∀ (u : D.what₂.Word) (pb : 𝓞 D.host.E), (pb : D.host.E) = D.host.conj ((aT u).piU : D.host.E) →
    ((H.lev0 u).Lb ⊔ Ideal.span {pb} • Submodule.span (𝓞 D.host.E)
        (dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 (H.lev0 u).Lb) = D.sp.crdLat0 (D.sp.X 0).L0) ∧
    ∀ (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m),
      (H.lev u i h1 hm).Lb ⊔ Ideal.span {pb} • dualL D.sp.cm (D.sp.X i) (H.lev u i h1 hm).Lb =
        crdLat (D.sp.X i) (D.sp.X i).L0

structure ColsHerm (D : ColRec) where
  base : HermCols D
  atT : ∀ u, AtT D u (base.vT u) (base.Fv u)
  levelZeroCompatibility : Lev0Tied D base atT
  ad : AdTied D base atT
  cof : CofTied D base atT
  piG : PiGConst D base atT levelZeroCompatibility
  stabMap : StabMapTied D base atT
  fvI : FvStepTied D base atT
  std : StdTied D
  baseL : BaseTied D base atT

end Formalism.L2.Col.CH

end
end

section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Col.CF

open Formalism.L2.Forms

section Step

variable (D : ColRec)

def sigD : D.host.E →ₐ[D.host.F] D.host.E := letI := D.host.cmStar; D.sp.cm.sig

def embT : D.what₂.Tau → D.host.E →+* ℂ := fun τ => D.host.emb (D.eTau τ : D.R.GG)

theorem rankN (i : ℕ) (hi : i ≤ D.R.m) : letI := D.host.cmStar; (D.sp.X i).rank = D.R.N i :=
  letI := D.host.cmStar; D.sp.X_rank i hi

def gramN (i : ℕ) (hi : i ≤ D.R.m) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E :=
  letI := D.host.cmStar
  (D.sp.X i).gram.reindex (finCongr (rankN D i hi)) (finCongr (rankN D i hi))

def clsCrd (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) :=
  letI := D.host.cmStar
  (D.clsLat u i c).map ((((D.sp.X i).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm) :
      (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)) :
      (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E))

def selfDualLatticeCoords (i : ℕ) (hi : i ≤ D.R.m) : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) :=
  letI := D.host.cmStar
  (D.sp.X i).L0.map ((((D.sp.X i).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm) :
      (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)) :
      (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E))

def badG : Set (HeightOneSpectrum (𝓞 D.host.F)) :=
  {v | (D.host.g 0 : 𝓞 D.host.F) ∈ v.asIdeal ∨ (D.host.g 1 : 𝓞 D.host.F) ∈ v.asIdeal}

abbrev PlT (u : D.what₂.Word) : Type :=
  {v : HeightOneSpectrum (𝓞 D.host.F) // (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal}

abbrev Fr (i : ℕ) (hi : i ≤ D.R.m) : Type := Frames (gramC (gramN D i hi) (embT D))

def RatSpan {n : ℕ} (lam : D.what₂.Tau → DomWeight n) :
    AddSubgroup (MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) :=
  AddSubgroup.closure {p | ∃ (r : D.what₂.LL) (f : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ),
    (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧
    p = D.what₂.embLL r • ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ))}

def IntSpan {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n) :
    AddSubgroup (MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) :=
  AddSubgroup.closure {p | ∃ (r : D.what₂.LL) (f : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ),
    r ∈ intW D.what₂.places w ∧ (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧
    p = D.what₂.embLL r • ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ))}

variable {D}

def lamT (u : D.what₂.Word) (i : ℕ) : D.what₂.Tau → DomWeight (D.R.N i) :=
  fun τ => shW ((D.fm u).lam i τ) ((i * (D.R.t + 1) / 2 : ℕ) : ℤ)

theorem lamT_zero (u : D.what₂.Word) : lamT u 0 = (D.fm u).lam 0 := by
  funext τ
  simp [lamT, shW_zero]

set_option maxHeartbeats 1000000 in

structure ClsTied (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) where

  lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) (D.mem u).A.T D.R.f (badG D)

  y : (D.mem u).C.cls i → UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  y_bij : Function.Bijective (fun c => (Quotient.mk'' (y c) : Cls lev))

  y_lat : ∀ c (x : Fin (D.R.N i) → D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
    x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F))
      (clsCrd D u i hi c) ↔
    ((y c).1⁻¹).1 *ᵥ x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) lev.Lb

  stabI : ∀ c, (D.mem u).C.stab i c →* UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)
  stabI_inj : ∀ c, Function.Injective (stabI c)
  stabI_range : ∀ c (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)),
    γ ∈ (stabI c).range ↔
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 ∈
        lev.U.map (MulAut.conj (y c).1).toMonoidHom

set_option maxHeartbeats 1000000 in

structure ValTied (u : D.what₂.Word) (eV : (D.mem u).A.vT ≃ PlT D u) (i : ℕ) (hi : i ≤ D.R.m) (K : ClsTied u i hi) where

  eY : (D.mem u).C.Y i ≃ Fr D i hi

  de : ∃ C : GL (Fin (D.R.N i)) D.host.E,
    cT (sigD D : D.host.E →+* D.host.E) C.1 * C.1 = gramN D i hi ∧
    (∀ x : Fin (D.R.N i) → D.host.E, x ∈ selfDualLatticeCoords D i hi ↔ ∀ a, (C.1 *ᵥ x) a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) ∧
    ∀ τ z, (D.mem u).C.de i z τ = embT D τ C.1.det * ((eY z).1 τ).det

  Fi : ∀ φ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ, φ ∈ (D.fm u).Fi i ↔
    (fun c z => φ c (eY.symm z)) ∈ FiC K.lev (embT D) (lamT u i) K.y

  ipV : ∀ c (o : Fr D i hi), o.IsON → ∀ P ∈ CSpan ((D.fm u).lam i), ∀ Q ∈ CSpan ((D.fm u).lam i),
    (D.fm u).ipV i c
      (fun z => fnOf _ (shiftOf (lamT u i)) (fun τ => (o.1 τ)⁻¹) P (eY z))
      (fun z => fnOf _ (shiftOf (lamT u i)) (fun τ => (o.1 τ)⁻¹) Q (eY z)) =
    nfAll ((D.fm u).lam i) Q P

  rat : ∀ φ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ, (∃ x, (D.fm u).emb i x = φ) ↔
    φ ∈ (D.fm u).Fi i ∧ ∀ c, ∃ P ∈ RatSpan D ((D.fm u).lam i),
      ∀ z, φ c z = fnOf _ (shiftOf (lamT u i)) 1 P (eY z)

  lat : ∀ x : ((D.fm u).lat i).V, x ∈ ((D.fm u).lat i).L ↔
    ∀ (w : D.what₂.places.Pl) (c : (D.mem u).C.cls i) (B : GL (Fin (D.R.N i)) D.host.E),
      IsLocBasis (D.what₂.places.resChar w)
        (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (clsCrd D u i hi c)) B →
      ∃ P ∈ IntSpan D w ((D.fm u).lam i),
        ∀ z, (D.fm u).emb i x c z =
          fnOf _ (shiftOf (lamT u i)) (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N i)) D.host.E).1) P (eY z)

  dil : ∀ v (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ), (k : (D.mem u).A.Fv v) = a → ∀ c δ,
    IsDia K.lev (eV v).1 (eV v).2 k δ →
    (Quotient.mk'' (K.y ((D.fm u).dil i v a c)) : Cls K.lev) = Quotient.mk'' (K.y c * δ)

  dilT : ∀ v (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ), (k : (D.mem u).A.Fv v) = a → ∀ c δ,
    IsDia K.lev (eV v).1 (eV v).2 k δ → ∀ g ∈ AdFun K.lev (embT D),
    (D.fm u).dilT i v a c (fun z => g (K.y ((D.fm u).dil i v a c)) (eY z)) = fun z => g (K.y c * δ) (eY z)

end Step

section AtT

variable {D : ColRec}

structure AtTTied (u : D.what₂.Word) where

  eV : (D.mem u).A.vT ≃ PlT D u

  piU : 𝓞 D.host.E
  piU_K : (piU : D.host.E) ∈ D.host.K
  piU_norm : (piU : D.host.E) * D.host.conj piU = ((D.mem u).A.T : D.host.E)
  piU_cong : piU - 1 ∈ Ideal.span
    {((D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) : 𝓞 D.host.E)}

  res : ∀ v, 𝓞 D.host.E →+* (D.mem u).A.Fv v
  res_surj : ∀ v, Function.Surjective (res v)
  res_pi : ∀ v, res v piU = 0

  res_conj : ∀ v (pb : 𝓞 D.host.E), (pb : D.host.E) = D.host.conj piU → res v pb ≠ 0
  res_v : ∀ v (x : 𝓞 D.host.F), x ∈ (eV v).1.asIdeal ↔ res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = 0

  tauOf : ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → ∀ v (x : 𝓞 D.host.F),
    x ∈ (eV v).1.asIdeal ↔ (0 : WithTop ℤ) < D.what₂.places.val w
      (D.embE (D.host.sigmaOf (D.eTau ((D.fm u).tauOf w v) : D.R.GG)
        (algebraMap (𝓞 D.host.F) D.host.E x)))

  seenP : ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → ∀ τ : D.what₂.Tau,
    (0 : WithTop ℤ) < D.what₂.places.val w (D.embE (D.host.sigmaOf (D.eTau τ : D.R.GG)
      (if (D.fm u).seenP w = true then (piU : D.host.E) else D.host.conj piU)))

def AtTTied.Pv {u : D.what₂.Word} (A : AtTTied u) (v : (D.mem u).A.vT) : Ideal (𝓞 D.host.E) := RingHom.ker (A.res v)

instance {u : D.what₂.Word} (A : AtTTied u) (v : (D.mem u).A.vT) : (A.Pv v).IsPrime := RingHom.ker_isPrime _

abbrev Ld (D : ColRec) (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) :=
  dualL (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (clsCrd D u i hi c)

abbrev Lk {u : D.what₂.Word} (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) :
    Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) :=
  clsCrd D u i hi c ⊔ A.Pv v • Ld D u i hi c

set_option maxHeartbeats 1000000 in

structure LvTied (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) where

  pr : ∀ v c, ↥(Ld D u i hi c) →+ (D.fm u).lv i v c
  pr_surj : ∀ v c, Function.Surjective (pr v c)
  pr_smul : ∀ v c (a : 𝓞 D.host.E) z, pr v c (a • z) = A.res v a • pr v c z
  pr_ker : ∀ v c z, pr v c z = 0 ↔ z.1 ∈ A.Pv v • Ld D u i hi c

  fv_ker : ∀ v c z, (D.fm u).fv i v c (pr v c z) = 0 ↔ z.1 ∈ Lk A i hi v c

  prk : ∀ v c, ↥(Lk A i hi v c) →+ (D.fm u).lk i v c
  prk_surj : ∀ v c, Function.Surjective (prk v c)
  prk_smul : ∀ v c (a : 𝓞 D.host.E) z, prk v c (a • z) = A.res v a • prk v c z
  prk_ker : ∀ v c z, prk v c z = 0 ↔ z.1 ∈ A.Pv v • Lk A i hi v c

  te : ∀ v c (z : ↥(Ld D u i hi c)), (D.fm u).fv i v c (pr v c z) = 1 →
    ∀ h : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z.1 ∈ Lk A i hi v c, prk v c ⟨_, h⟩ = (D.fm u).te i v c

variable {u : D.what₂.Word} {A : AtTTied u} {i : ℕ} {hi : i ≤ D.R.m}

set_option maxHeartbeats 1000000 in

def FvTie (P : LvTied u A i hi) (K : ClsTied u i hi)
    (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v) : Prop :=
  ∀ v c (z : ↥(Ld D u i hi c))
    (hz : ((bc (prV (E := D.host.E) (A.eV v).1) (K.y c).1)⁻¹).1 *ᵥ
        (fun a => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (z.1 a)) ∈
      latS (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (intV D.host.E (A.eV v).1)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) K.lev.Lb))),
    (D.fm u).fv i v c (P.pr v c z) = fMe v (K.lev.fT (A.eV v).1 (A.eV v).2 ⟨_, hz⟩)

set_option maxHeartbeats 1000000 in

def UpNatTie (P : LvTied u A i hi) (K : ClsTied u i hi) (W : ValTied u A.eV i hi K) : Prop :=
  ∀ v c (z : ↥(Ld D u i hi c)), (D.fm u).fv i v c (P.pr v c z) = 1 →
    ∃ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
      (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : K.lev.U),
      (∀ v', v' ≠ (A.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) ∧
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
        (K.y ((D.fm u).up i v c (P.pr v c z))).1 = (K.y c).1 * η.1 * κ.1 ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).up i v c (P.pr v c z)))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Ld D u i hi c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat γ.1.1 (Ld D u i hi ((D.fm u).up i v c (P.pr v c z)))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Ld D u i hi c ⊔
          Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) ∧
      (∀ (x : ↥(Ld D u i hi ((D.fm u).up i v c (P.pr v c z))))
        (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ Ld D u i hi c),
        (D.fm u).fv i v _ (P.pr v _ x) = (D.fm u).fv i v c (P.pr v c ⟨_, hx⟩)) ∧
      ∀ (h : (D.mem u).C.Y i → ℂ) s s', IsTr (atInf (embT D) γ.1.1) (W.eY s') (W.eY s) →
        (D.fm u).upT i v c (P.pr v c z) h s = (((K.lev.chi κ)⁻¹ : ℂˣ) : ℂ) * h s'

set_option maxHeartbeats 1000000 in

def DnNatTie (P : LvTied u A i hi) (K : ClsTied u i hi) (W : ValTied u A.eV i hi K) : Prop :=
  ∀ v c (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)), g ≠ 0 →
    ∃ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
      (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : K.lev.U),
      (∀ v', v' ≠ (A.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) ∧
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
        (K.y ((D.fm u).dn i v c g)).1 = (K.y c).1 * η.1 * κ.1 ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat γ.1.1 (Ld D u i hi ((D.fm u).dn i v c g))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (clsCrd D u i hi c) ∧
      (∀ (x : ↥(Ld D u i hi ((D.fm u).dn i v c g))) (hx : γ.1.1 *ᵥ x.1 ∈ Lk A i hi v c),
        (D.fm u).fv i v _ (P.pr v _ x) = g (P.prk v c ⟨_, hx⟩)) ∧
      ∀ (h : (D.mem u).C.Y i → ℂ) s s', IsTr (atInf (embT D) γ.1.1) (W.eY s') (W.eY s) →
        (D.fm u).dnT i v c g h s = (((K.lev.chi κ)⁻¹ : ℂˣ) : ℂ) * h s'

end AtT

end Formalism.L2.Col.CF

end
end

section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Col.CF

open Formalism.L2.Forms

section XP

variable (D : ColRec)

theorem rankP : letI := D.host.cmStar; D.sp.X'.rank = D.R.N D.R.m - 1 := by
  letI := D.host.cmStar
  have h := D.sp.X'_rank
  have h2 := D.R.m_add_three_le_k
  rw [h]; unfold Ranks.rankX' Ranks.r Ranks.N; rw [Nat.mul_add, Nat.mul_one]; omega

def gramP : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E :=
  letI := D.host.cmStar
  D.sp.X'.gram.reindex (finCongr (rankP D)) (finCongr (rankP D))

def iXc : (Fin (D.R.N D.R.m - 1) → D.host.E) →ₗ[D.host.E] (Fin (D.R.N D.R.m) → D.host.E) :=
  letI := D.host.cmStar
  ((((D.sp.X D.R.m).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D D.R.m le_rfl)).symm) :
      (D.sp.X D.R.m).V ≃ₗ[D.host.E] (Fin (D.R.N D.R.m) → D.host.E)) :
      (D.sp.X D.R.m).V →ₗ[D.host.E] (Fin (D.R.N D.R.m) → D.host.E)).comp D.sp.iX').comp
    ((D.sp.X'.frame.equivFun.trans
      (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)).symm :
      (Fin (D.R.N D.R.m - 1) → D.host.E) →ₗ[D.host.E] D.sp.X'.V)

def zc : Fin (D.R.N D.R.m) → D.host.E :=
  letI := D.host.cmStar
  ((D.sp.X D.R.m).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D D.R.m le_rfl)).symm)) D.sp.z

def iXm : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m - 1)) D.host.E := LinearMap.toMatrix' (iXc D)

def IsExt (z0 : Fin (D.R.N D.R.m) → D.host.E) {R : Type} [CommRing R] (φ : D.host.E →+* R)
    (g' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) R)
    (g : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) R) : Prop :=
  g * (iXm D).map φ = (iXm D).map φ * g' ∧ g *ᵥ (fun a => φ (z0 a)) = fun a => φ (z0 a)

abbrev FrP : Type := Frames (gramC (gramP D) (embT D))

variable {D}

set_option maxHeartbeats 1000000 in

structure ClsPTied (u : D.what₂.Word) where

  lev : StepLevel D.host.F D.host.E (sigD D) (gramP D) 1 D.R.f (badG D)
  y : (D.fm u).clsP → UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  y_bij : Function.Bijective (fun c => (Quotient.mk'' (y c) : Cls lev))

  lat : (D.fm u).clsP → Submodule (𝓞 D.host.E) (Fin (D.R.N D.R.m - 1) → D.host.E)
  y_lat : ∀ c (x : Fin (D.R.N D.R.m - 1) → D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
    x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F))
      (lat c) ↔
    ((y c).1⁻¹).1 *ᵥ x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) lev.Lb
  lat_fin : ∀ c, Module.Finite (𝓞 D.host.E) (lat c)
  stabI : ∀ c, (D.fm u).stabilizer₂ c →* UJ (sigD D : D.host.E →+* D.host.E) (gramP D)
  stabI_inj : ∀ c, Function.Injective (stabI c)
  stabI_range : ∀ c (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramP D)),
    γ ∈ (stabI c).range ↔
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 ∈
        lev.U.map (MulAut.conj (y c).1).toMonoidHom

def sgT (u : D.what₂.Word) : D.what₂.Tau → DomWeight (D.R.N D.R.m - 1) :=
  fun τ => shW ((D.fm u).sg τ) ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ)

set_option maxHeartbeats 1000000 in

structure ValPTied (u : D.what₂.Word) (K : ClsPTied u) where

  sg : ∀ τ (i : Fin (D.R.N D.R.m - 1)),
    (((D.fm u).sg τ).w i : ℚ) = sgHC D.R (D.hcW u τ) i - rhoVec (D.R.N D.R.m - 1) i

  eW : (D.mem u).P.Wrow ≃ₗ[ℂ] ((D.fm u).clsP → FrP D → ℂ)
  ptC : ∀ z, z ∈ (D.fm u).ptC ↔ eW z ∈ FiC K.lev (embT D) (sgT u) K.y

  ipP : ∀ (o : FrP D), o.IsON → ∀ (z z' : (D.mem u).P.Wrow)
    (P Q : (D.fm u).clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ),
    (∀ c, P c ∈ CSpan (D.fm u).sg) → (∀ c, Q c ∈ CSpan (D.fm u).sg) →
    (∀ c, eW z c = fnOf _ (shiftOf (sgT u)) (fun τ => (o.1 τ)⁻¹) (P c)) →
    (∀ c, eW z' c = fnOf _ (shiftOf (sgT u)) (fun τ => (o.1 τ)⁻¹) (Q c)) →
    (D.fm u).ipP z z' = ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℂ)⁻¹ * nfAll (D.fm u).sg (Q c) (P c)
  rat : ∀ z, (∃ x, (D.fm u).ptEmb x = z) ↔
    z ∈ (D.fm u).ptC ∧ ∀ c, ∃ P ∈ RatSpan D (D.fm u).sg, eW z c = fnOf _ (shiftOf (sgT u)) 1 P

  lat : ∀ x : (D.fm u).ptLat.V, x ∈ (D.fm u).ptLat.L ↔
    ∀ (w : D.what₂.places.Pl) (c : (D.fm u).clsP) (B : GL (Fin (D.R.N D.R.m - 1)) D.host.E),
      IsLocBasis (D.what₂.places.resChar w) (K.lat c : Set _) B →
      ∃ P ∈ IntSpan D w (D.fm u).sg, eW ((D.fm u).ptEmb x) c =
        fnOf _ (shiftOf (sgT u)) (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N D.R.m - 1)) D.host.E).1) P

set_option maxHeartbeats 1000000 in

structure TilTied (u : D.what₂.Word) (A : AtTTied u) (K : ClsPTied u) (P : LvTied u A D.R.m le_rfl) where
  z0 : Fin (D.R.N D.R.m) → D.host.E
  lastCoordinateUniformizerVector_spans_orthogonal_line : ∃ a : D.host.E, z0 = a • zc D
  hermitianForm_lastCoordinateUniformizerVector_self : hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) z0 z0 = ((D.mem u).A.T : D.host.E)
  ga : (D.fm u).clsP → UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)
  til_lat : ∀ c, mulLat (ga c).1.1 (clsCrd D u D.R.m le_rfl ((D.fm u).til c)) =
    (K.lat c).map ((iXc D).restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {z0}
  til_fv : ∀ v c (x : ↥(Ld D u D.R.m le_rfl ((D.fm u).til c))) (r : 𝓞 D.host.E),
    (r : D.host.E) = hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) z0 ((ga c).1.1 *ᵥ x.1) →
    (D.fm u).fv D.R.m v ((D.fm u).til c) (P.pr v _ x) = A.res v r

set_option maxHeartbeats 4000000 in

def TilBaseLat {u : D.what₂.Word} {A : AtTTied u} {K : ClsPTied u} {P : LvTied u A D.R.m le_rfl}
    (Tl : TilTied u A K P) (Km : ClsTied u D.R.m le_rfl) : Prop :=
  Km.lev.Lb = K.lev.Lb.map ((iXc D).restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {Tl.z0}

set_option maxHeartbeats 4000000 in

def TilBaseFv {u : D.what₂.Word} {A : AtTTied u} {K : ClsPTied u} {P : LvTied u A D.R.m le_rfl}
    (Tl : TilTied u A K P) (Km : ClsTied u D.R.m le_rfl)
    (fMe : ∀ v, Km.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v) : Prop :=
  ∀ v (t : latS (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (intV D.host.E (A.eV v).1)
      (Submodule.span (𝓞 D.host.E)
        (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) Km.lev.Lb)))
    (x : Fin (D.R.N D.R.m) → D.host.E) (r : 𝓞 D.host.E),
    t.1 = (fun a => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (x a)) →
    (r : D.host.E) = hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) Tl.z0 x →
    fMe v (Km.lev.fT (A.eV v).1 (A.eV v).2 t) = A.res v r

set_option maxHeartbeats 4000000 in

structure TilAd {u : D.what₂.Word} {A : AtTTied u} {K : ClsPTied u} {P : LvTied u A D.R.m le_rfl}
    (Tl : TilTied u A K P) (Km : ClsTied u D.R.m le_rfl) where
  ka : (D.fm u).clsP → Km.lev.U
  til_ad : ∀ c (g : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
    IsExt D Tl.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (K.y c).1.1 g.1 →
    bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Tl.ga c).1 * (Km.y ((D.fm u).til c)).1 =
      g * (ka c).1

set_option maxHeartbeats 4000000 in

def FrExt {u : D.what₂.Word} (z0 : Fin (D.R.N D.R.m) → D.host.E) {K : ClsPTied u} {Km : ClsTied u D.R.m le_rfl}
    {G : GLoc D.host.F D.host.E (sigD D) D.host.g} {a t nb sk fc a' t' nb' sk' fc' : ℕ} {zl zl' : Bool}
    (Lm : GLev Km.lev G a t nb sk fc zl) (Lp : GLev K.lev G a' t' nb' sk' fc' zl') : Prop :=
  ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal),
    (∀ (x : Fin (D.R.N D.R.m)) (b : Fin (D.R.N D.R.m - 1)) (b' : Fin (D.R.N D.R.m)), (b : ℕ) = b' →
      (Lm.fr i v h).1 x b' =
        ((iXm D).map ((G.phi i v h).comp (inclE (F := D.host.F) (v.adicCompletion D.host.F))) * (Lp.fr i v h).1) x b) ∧
    ∀ (x l : Fin (D.R.N D.R.m)), (l : ℕ) + 1 = D.R.N D.R.m →
      (Lm.fr i v h).1 x l = G.phi i v h (inclE (F := D.host.F) (v.adicCompletion D.host.F) (z0 x))

end XP

section All

variable {D : ColRec}

def EvzTie {u : D.what₂.Word} {A : AtTTied u} {K : ClsPTied u} {P : LvTied u A D.R.m le_rfl}
    {Tl : TilTied u A K P} {Km : ClsTied u D.R.m le_rfl}
    (Ta : TilAd Tl Km) (W : ValTied u A.eV D.R.m le_rfl Km)
    (eWz : (D.mem u).P.Wz ≃ₗ[ℂ] ((D.fm u).clsP → (D.mem u).C.Y D.R.m → ℂ)) : Prop :=
  ∀ (φ : (D.mem u).C.cls D.R.m → (D.mem u).C.Y D.R.m → ℂ) c s s',
    IsTr (atInf (embT D) (Tl.ga c).1.1) (W.eY s') (W.eY s) →
    eWz ((D.mem u).P.evz φ) c s = (((Km.lev.chi (Ta.ka c))⁻¹ : ℂˣ) : ℂ) * φ ((D.fm u).til c) s'

open Classical in

def BwTie {u : D.what₂.Word} (A : AtTTied u) {i : ℕ} {hi : i ≤ D.R.m} {K : ClsTied u i hi}
    (W : ValTied u A.eV i hi K) : Prop :=
  ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → (D.fm u).seenP w = true →
    ∀ v (x : ((D.fm u).lat i).V), x ∈ (D.fm u).Bw i w v ↔
    ∀ (c : (D.mem u).C.cls i) (B B' : GL (Fin (D.R.N i)) D.host.E),
      IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B → IsLocBasis (D.mem u).A.T (Lk A i hi v c : Set _) B' →
      ∃ P ∈ IntSpan D w ((D.fm u).lam i), ∀ z, (D.fm u).emb i x c z =
        fnOf _ (shiftOf (lamT u i))
          (fun τ => if τ = (D.fm u).tauOf w v then atInf (embT D) (B'⁻¹ : GL (Fin (D.R.N i)) D.host.E).1 τ
            else atInf (embT D) (B⁻¹ : GL (Fin (D.R.N i)) D.host.E).1 τ) P (W.eY z)

def PerTie (u : D.what₂.Word) (jM : (D.mem u).P.Mt →ₛₗ[starRingEnd ℂ] (D.mem u).P.Wrow) : Prop :=
  (∀ z ∈ (D.fm u).ptC, ∃ F, jM F = z) ∧ (∀ F, jM F ∈ (D.fm u).ptC) ∧
    ∀ w F, (D.mem u).P.period w F = (D.fm u).ipP (jM F) w

def embS (D : ColRec) (s : D.what₂.LL →+* ℂ) : D.what₂.Tau → D.host.E →+* ℂ :=
  fun τ => s.comp (D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E))

def NormTie {u : D.what₂.Word} {eV : (D.mem u).A.vT ≃ PlT D u} {i : ℕ} {hi : i ≤ D.R.m} {K : ClsTied u i hi}
    (W : ValTied u eV i hi K) : Prop :=
  ∀ (s : D.what₂.LL →+* ℂ) (x : ((D.fm u).lat i).V)
    (Pc : (D.mem u).C.cls i → MvPolynomial (D.what₂.Tau × Fin (D.R.N i) × Fin (D.R.N i)) D.what₂.LL),
    (∀ c z, (D.fm u).emb i x c z =
      fnOf _ (shiftOf (lamT u i)) 1 (MvPolynomial.map D.what₂.embLL (Pc c)) (W.eY z)) →
    ∀ o : Frames (gramC (gramN D i hi) (embS D s)), o.IsON →
      (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat i).b ((D.fm u).lat i).X (InfinitePlace.mk s) x x).re =
        ∑ c, ((D.mem u).C.wt i c).re * (∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf (lamT u i) τ)) *
          (nfAll ((D.fm u).lam i) (subP o.1 (MvPolynomial.map s (Pc c))) (subP o.1 (MvPolynomial.map s (Pc c)))).re

def NormPTie {u : D.what₂.Word} {K : ClsPTied u} (W : ValPTied u K) : Prop :=
  ∀ (s : D.what₂.LL →+* ℂ) (x : (D.fm u).ptLat.V)
    (Pc : (D.fm u).clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) D.what₂.LL),
    (∀ c, W.eW ((D.fm u).ptEmb x) c =
      fnOf _ (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL (Pc c))) →
    ∀ o : Frames (gramC (gramP D) (embS D s)), o.IsON →
      (Formalism.HermitianLatticesTheory.majAt (D.fm u).ptLat.b (D.fm u).ptLat.X (InfinitePlace.mk s) x x).re =
        ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℝ)⁻¹ * (∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf (sgT u) τ)) *
          (nfAll (D.fm u).sg (subP o.1 (MvPolynomial.map s (Pc c))) (subP o.1 (MvPolynomial.map s (Pc c)))).re

set_option maxHeartbeats 1000000 in

structure FormsTied (D : ColRec) (u : D.what₂.Word) where
  atT : AtTTied u
  cls : ∀ i hi, ClsTied u i hi
  val : ∀ i hi, ValTied u atT.eV i hi (cls i hi)

  gl : GLoc D.host.F D.host.E (sigD D) D.host.g
  gl_K : ∀ i, (gl.piG i : D.host.E) ∈ D.host.K

  glev : ∀ i hi, GLev (cls i hi).lev gl (aOf D.R i) D.R.t i (skipOf D.R i) (fcOf D.R i) (decide (i = D.R.m))
  lv : ∀ i hi, LvTied u atT i hi
  fMe : ∀ i hi v, (cls i hi).lev.fM (atT.eV v).1 (atT.eV v).2 ≃+ (D.mem u).A.Fv v
  fv : ∀ i hi, FvTie (lv i hi) (cls i hi) (fMe i hi)

  upN : ∀ i hi, UpNatTie (lv i hi) (cls i hi) (val i hi)
  dnN : ∀ i hi, DnNatTie (lv i hi) (cls i hi) (val i hi)
  norm : ∀ i hi, NormTie (val i hi)
  bw : ∀ i hi, BwTie atT (val i hi)
  clsP : ClsPTied u
  valP : ValPTied u clsP
  normP : NormPTie valP

  glevP : GLev clsP.lev gl D.R.r D.R.t D.R.m (D.R.N D.R.m) (fcOf D.R D.R.m) false
  til : TilTied u atT clsP (lv D.R.m le_rfl)
  tilLat : TilBaseLat til (cls D.R.m le_rfl)
  tilFv : TilBaseFv til (cls D.R.m le_rfl) (fMe D.R.m le_rfl)
  tilAd : TilAd til (cls D.R.m le_rfl)
  frExt : FrExt til.z0 (glev D.R.m le_rfl) glevP
  eWz : (D.mem u).P.Wz ≃ₗ[ℂ] ((D.fm u).clsP → (D.mem u).C.Y D.R.m → ℂ)
  evz : EvzTie tilAd (val D.R.m le_rfl) eWz
  jM : (D.mem u).P.Mt →ₛₗ[starRingEnd ℂ] (D.mem u).P.Wrow
  per : PerTie u jM

  DGam : (D.mem u).C.DGam = (D.mem D.u₀).C.DGam

end All

end Formalism.L2.Col.CF

end
end

section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Col.CF

open Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def crdN (D : ColRec) (i : ℕ) (hi : i ≤ D.R.m) : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E) :=
  (D.sp.X i).frame.equivFun.trans (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm)

def crdP (D : ColRec) : D.sp.X'.V ≃ₗ[D.host.E] (Fin (D.R.N D.R.m - 1) → D.host.E) :=
  D.sp.X'.frame.equivFun.trans (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)

set_option maxHeartbeats 4000000 in

structure Joint {D : ColRec} (X : CH.ColsHerm D) (u : D.what₂.Word) (T : FormsTied D u) : Prop where

  eV : T.atT.eV = X.base.vT u
  piU : T.atT.piU = (X.atT u).piU
  res : T.atT.res = (X.atT u).res

  car0 : SameCar (rank_eq_first_level D.R) (X.base.lev0 u).Lb (T.cls 0 (Nat.zero_le _)).lev.Lb
    (X.base.lev0 u).Uloc (T.cls 0 (Nat.zero_le _)).lev.Uloc (X.base.lev0 u).U (T.cls 0 (Nat.zero_le _)).lev.U
    (fun c => ((X.base.lev0 u).y c).1) (fun c => ((T.cls 0 (Nat.zero_le _)).y c).1)
    (fun c s => ((X.base.lev0 u).stabI c s).1) (fun c s => ((T.cls 0 (Nat.zero_le _)).stabI c s).1)

  carI : ∀ (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m), SameCar (rankN D i hm) (X.base.lev u i h1 hm).Lb (T.cls i hm).lev.Lb
    (X.base.lev u i h1 hm).Uloc (T.cls i hm).lev.Uloc (X.base.lev u i h1 hm).U (T.cls i hm).lev.U
    (fun c => ((X.base.cls u i h1 hm).y c).1) (fun c => ((T.cls i hm).y c).1)
    (fun c s => ((X.base.cls u i h1 hm).stabI c s).1) (fun c s => ((T.cls i hm).stabI c s).1)

  carP : SameCar (rankP D) (Formalism.L2.Herm.crdLat D.sp.X' D.sp.X'.L0) T.clsP.lev.Lb
    (X.atT u).levP.Uloc T.clsP.lev.Uloc (X.atT u).levP.U T.clsP.lev.U
    (fun c => ((X.atT u).clsP.y c).1) (fun c => (T.clsP.y c).1)
    (fun c s => ((X.atT u).clsP.stabI c s).1) (fun c s => (T.clsP.stabI c s).1)
  lattice₂ : ∀ c, T.clsP.lat c = ((X.atT u).lattice₂ c).map
    ((crdP D : D.sp.X'.V →ₗ[D.host.E] (Fin (D.R.N D.R.m - 1) → D.host.E)).restrictScalars (𝓞 D.host.E))

  pr : ∀ (i : ℕ) (hi : i ≤ D.R.m) v c (z : CH.Ld D u i c) (z' : Ld D u i hi c),
    z'.1 = crdN D i hi z.1 → (T.lv i hi).pr v c z' = (X.atT u).pr i v c z
  prk : ∀ (i : ℕ) (hi : i ≤ D.R.m) v c (z : CH.Lk D u ((X.atT u).Pv v) i c) (z' : Lk T.atT i hi v c),
    z'.1 = crdN D i hi z.1 → (T.lv i hi).prk v c z' = (X.atT u).prk i v c z

  z0 : T.til.z0 = crdN D D.R.m le_rfl (X.atT u).z0
  ga : ∀ c, (T.til.ga c).1 = reGL (rankN D D.R.m le_rfl) _
    (Formalism.L2.Herm.toGLb (D.sp.X D.R.m).frame ((X.atT u).tilG c).1)

  sp : T.gl.sp = (X.base.lev0 u).splitG
  piG : T.gl.piG = (X.levelZeroCompatibility u).piG
  fr0 : ∀ i v h, (T.glev 0 (Nat.zero_le _)).fr i v h = reGL (rank_eq_first_level D.R) _ ((X.base.lev0 u).frG i v h)

structure ColsTied (D : ColRec) where
  herm : CH.ColsHerm D
  forms : ∀ u : D.what₂.Word, FormsTied D u
  joint : ∀ u, Joint herm u (forms u)
  gl_const : ∀ u u', (forms u).gl = (forms u').gl

  chi : CharacterCompatible (forms D.u₀).gl D.R.m

  fr_const : ∀ u u' (i : ℕ) (hi : i ≤ D.R.m), i < D.R.m → ((forms u).glev i hi).fr = ((forms u').glev i hi).fr
  frP_const : ∀ u u', (forms u).glevP.fr = (forms u').glevP.fr

end Formalism.L2.Col.CF

end
end
