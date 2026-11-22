module

public import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Forms0 (D : D7) (u : D.what₂.Word) where
  atT : AtTTied u

  cls0 : ClsTied u 0 (Nat.zero_le _)

  val0 : ValTied u atT.eV 0 (Nat.zero_le _) cls0

  gl : GLoc D.host.F D.host.E (sigD D) D.host.g
  gl_K : ∀ i, (gl.piG i : D.host.E) ∈ D.host.K

  glev0 : GLev cls0.lev gl D.R.k D.R.t 0 D.R.k (D.R.N 0) false

  lv0 : LvTied u atT 0 (Nat.zero_le _)
  fMe0 : ∀ v, cls0.lev.fM (atT.eV v).1 (atT.eV v).2 ≃+ (D.mem u).A.Fv v
  fv0 : FvTie lv0 cls0 fMe0
  up_natural_level_zero : UpNatTie lv0 cls0 val0
  down_natural_level_zero : DnNatTie lv0 cls0 val0
  norm0 : NormTie val0
  bw0 : BwTie atT val0

namespace Forms0

variable {D : D7} {u : D.what₂.Word} (T : Forms0 D u)

def cls : ∀ (i : ℕ) (hi : i ≤ D.R.m), i = 0 → ClsTied u i hi
  | 0, _, _ => T.cls0

def val : ∀ (i : ℕ) (hi : i ≤ D.R.m) (h : i = 0), ValTied u T.atT.eV i hi (T.cls i hi h)
  | 0, _, _ => T.val0

def lv : ∀ (i : ℕ) (hi : i ≤ D.R.m), i = 0 → LvTied u T.atT i hi
  | 0, _, _ => T.lv0

theorem norm : ∀ (i : ℕ) (hi : i ≤ D.R.m) (h : i = 0), NormTie (T.val i hi h)
  | 0, _, _ => T.norm0

theorem bw : ∀ (i : ℕ) (hi : i ≤ D.R.m) (h : i = 0), BwTie T.atT (T.val i hi h)
  | 0, _, _ => T.bw0

end Forms0

def Joint0 {D : D7} (L0 : LevelData D) (u : D.what₂.Word) (T : Forms0 D u) : Prop :=
  SameCar (rank_eq_first_level D.R) (L0 u).Lb T.cls0.lev.Lb (L0 u).Uloc T.cls0.lev.Uloc (L0 u).U T.cls0.lev.U
    (fun c => ((L0 u).y c).1) (fun c => (T.cls0.y c).1)
    (fun c s => ((L0 u).stabI c s).1) (fun c s => (T.cls0.stabI c s).1)

end Formalism.L2.Forms
