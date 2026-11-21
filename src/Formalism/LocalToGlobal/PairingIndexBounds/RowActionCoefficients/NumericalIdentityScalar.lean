import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.SuccMulSuccSubOneDivSucc
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.Bridge
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.YVMapRowAct
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.TgtBidet
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.GeXZero

section
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

abbrev BX : Type := Σ v : X.Pl, Fin (X.G.P.n' v)

abbrev NJ (j : ℕ) : ℕ := NN X.G.P.m X.t j

def emX (j : ℕ) (b : BX X) (v : Fin (NJ X j) × Fin (NJ X j)) :
    (Σ v : Fin (X.Fl.Pj j).nV, Fin ((X.Fl.Pj j).n' v) × (Fin ((X.Fl.Pj j).m + 1) × Fin ((X.Fl.Pj j).m + 1))) :=
  idxI X j ⟨b.1, (b.2, v)⟩

def xmX (j : ℕ) (b : BX X) (s : ℕ × Fin (NJ X j)) : X.FrI j := ⟨b.1, (b.2, s.1, s.2)⟩

def mF (j : ℕ) (b : BX X) (A : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq b.1)) :
    Matrix (Fin (NJ X j)) (Fin (NJ X j)) X.G.Kf :=
  (A.map fun x => X.G.P.ι b.1 ((X.G.P.σ b.1 ^ b.2.val) x)).submatrix (finCongr (rank_eq X j).symm) (finCongr (rank_eq X j).symm)

def nuM : (j : ℕ) → BX X → Fin (NJ X j) → ℕ
  | 0, b, t => nuOf (lamAt (X.G.P.lam0 b.1) b.2) (Fin.cast (rankJ X 0).symm t)
  | j + 1, b, t => nuOf (lamAt ((X.Fl.Pj (j + 1)).lam0 b.1) b.2) (Fin.cast (rankJ X (j + 1)).symm t)

def sX (j : ℕ) (g : ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) : X.G.Kf :=
  ∏ b : BX X, (mF X j b (g b.1)).det ^ (-(eJ X j b.1 b.2))

def muX (j n : ℕ) (b : BX X) : Fin n → ℕ := fun t => (X.nuv b.1 (j + 1) b.2 (t.val + 1)).toNat

def cX (j : ℕ) (b : BX X) : ℕ := (X.nuv b.1 (j + 1) b.2 1).toNat

def eX (j : ℕ) (b : BX X) : ℕ := (X.nuv b.1 (j + 1) b.2 (NJ X j)).toNat

def nuS (j : ℕ) (b : BX X) : Fin (NJ X j) → ℕ :=
  if IsOddPos b.2 then fun t => cX X j b - muX X j (NJ X j) b t.rev else fun t => muX X j (NJ X j) b t - eX X j b

def nuT (j : ℕ) (b : BX X) : Fin (NJ X (j + 1)) → ℕ :=
  if IsOddPos b.2 then fun t => cX X j b - muX X j (NJ X (j + 1)) b t.rev else muX X j (NJ X (j + 1)) b

def HgX (R : Type) [CommRing R] (j : ℕ) (b : BX X) : GenR R (NJ X j) :=
  if IsOddPos b.2 then hvO (gX R (NJ X j)) (gY R (NJ X j)) (cX X j b) (fun k => colH (muX X j (NJ X j) b) k.val)
  else (Matrix.of fun a i : Fin (NJ X j) => gX R (NJ X j) a i.val).det ^ (eX X j b) *
    hvE (gX R (NJ X j)) (gY R (NJ X j)) (cX X j b) (fun k => colH (nuS X j b) k.val) (fun k => colH_le _ k.val)

def szT (j : ℕ) (b : BX X) (k : Fin (cX X j b)) : ℕ :=
  if IsOddPos b.2 then NJ X (j + 1) - colH (muX X j (NJ X (j + 1)) b) k.val else colH (muX X j (NJ X (j + 1)) b) k.val

theorem szT_le (j : ℕ) (b : BX X) (k : Fin (cX X j b)) : szT X j b k ≤ NJ X (j + 1) := by
  unfold szT
  split_ifs
  · exact Nat.sub_le _ _
  · exact colH_le _ _

end Formalism.L2.PairingIndexBounds.Ent
end
end

section
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Defs

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def srcN (j : ℕ) (b : BX X) (x : Fin (NJ X j) → ℕ → X.G.Kf) : MvPolynomial (Fin (NJ X j) × Fin (NJ X j)) X.G.Kf :=
  if IsOddPos b.2 then hvO (fun a i => C (x a i)) (yV X.G.Kf (NJ X j)) (cX X j b) (fun k => colH (muX X j (NJ X j) b) k.val)
  else C ((Matrix.of fun a i : Fin (NJ X j) => x a i.val).det ^ (eX X j b)) *
    hvE (fun a i => C (x a i)) (yV X.G.Kf (NJ X j)) (cX X j b) (fun k => colH (nuS X j b) k.val) (fun k => colH_le _ k.val)

def tgtN (K' : Type) [CommRing K'] (j : ℕ) (b : BX X) (z : Fin (NJ X (j + 1)) → ℕ → K') :
    MvPolynomial (Fin (NJ X (j + 1)) × Fin (NJ X (j + 1))) K' :=
  if IsOddPos b.2 then
    hvO (fun a i => C (z a i)) (yV K' (NJ X (j + 1))) (cX X j b) (fun k => colH (muX X j (NJ X (j + 1)) b) k.val)
  else hvE (fun a i => C (z a i)) (yV K' (NJ X (j + 1))) (cX X j b) (fun k => colH (muX X j (NJ X (j + 1)) b) k.val)
    (fun k => colH_le _ k.val)

variable (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc]

def tgtD (j : ℕ) (b : BX X) (x : Fin (NJ X j) → ℕ → X.G.Kf) : DA X Kc j :=
  if IsOddPos b.2 then
    hvO (xd X Kc j b.1 b.2 x) (yMat X Kc j b.1 b.2) (cX X j b) (fun k => colH (muX X j (NJ X (j + 1)) b) k.val)
  else hvE (xd X Kc j b.1 b.2 x) (yMat X Kc j b.1 b.2) (cX X j b) (fun k => colH (muX X j (NJ X (j + 1)) b) k.val)
    (fun k => colH_le _ k.val)

def evD (j : ℕ) (d0 : X.ZA j → Kc) : DA X Kc j →+* XspC (X.Pj (j + 1)) Kc :=
  eval₂Hom (RingHom.id _) fun z => C (d0 z)

def dM (j : ℕ) (b : BX X) (d0 : X.ZA j → Kc) : Matrix (Fin (NJ X j)) (Fin (NJ X (j + 1))) Kc :=
  fun a b' => d0 ⟨b.1, (b.2, a, b')⟩

end Defs

def XShape : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (j : ℕ) (b : BX X),
    nuM X j b = nuS X j b ∧ nuM X (j + 1) b = nuT X j b ∧
    (∀ n, Antitone (muX X j n b)) ∧ (∀ n t, muX X j n b t ≤ cX X j b) ∧
    (∀ k, colH (muX X j (NJ X j) b) k = X.colHt b.1 (j + 1) b.2 k) ∧
    (∀ k, colH (muX X j (NJ X (j + 1)) b) k = X.colHt b.1 (j + 1) b.2 k) ∧
    (∀ t, eX X j b ≤ muX X j (NJ X j) b t) ∧ (∀ t : Fin (NJ X j), t.val + 1 = NJ X j → muX X j (NJ X j) b t = eX X j b) ∧
    (¬ IsOddPos b.2 → (eX X j b : ℤ) = eJ X j b.1 b.2 + X.w b.1 (j + 1) b.2 ∧ eJ X (j + 1) b.1 b.2 = -X.w b.1 (j + 1) b.2) ∧
    (IsOddPos b.2 → (cX X j b : ℤ) = X.w b.1 (j + 1) b.2 - eJ X j b.1 b.2 ∧ eJ X (j + 1) b.1 b.2 = eJ X j b.1 b.2)

def XBrS : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p), Function.Injective (algebraMap X.G.O X.G.Kf) →
    ∀ (j : ℕ) (L : (X.Pj j).Tup) (g : ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)),
      (∀ v, IsUnit (g v).det) → (∀ v, X.latAt v j L = colSpan (X.G.P.W v) (g v)) →
      ∀ T : Submodule X.G.O (X.Pj j).Xsp,
        (∀ F : BX X → MvPolynomial (Fin (NJ X j) × Fin (NJ X j)) X.G.Kf,
          (∀ b, F b ∈ deltaL X.G.O X.G.Kf (NJ X j) (nuM X j b) (mF X j b (g b.1))) →
            sX X j g • ∏ b, rename (emX X j b) (F b) ∈ T) → (X.Pj j).HtupW L ≤ T

def XBrT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p), Function.Injective (algebraMap X.G.O X.G.Kf) →
    ∀ (j : ℕ) (L : (X.Pj j).Tup) (g : ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)),
      (∀ v, IsUnit (g v).det) → (∀ v, X.latAt v j L = colSpan (X.G.P.W v) (g v)) →
      ∀ F : BX X → MvPolynomial (Fin (NJ X j) × Fin (NJ X j)) X.G.Kf,
        (∀ b, F b ∈ deltaL X.G.O X.G.Kf (NJ X j) (nuM X j b) (mF X j b (g b.1))) →
          sX X j g • ∏ b, rename (emX X j b) (F b) ∈ (X.Pj j).HtupW L

def XInj : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (j : ℕ),
    (Function.Injective fun x : BX X × (Fin (NJ X j) × Fin (NJ X j)) => emX X j x.1 x.2) ∧
    (Function.Injective fun x : BX X × (ℕ × Fin (NJ X j)) => xmX X j x.1 x.2)

def XA : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ)
    (x : ∀ b : BX X, Fin (NJ X j) → ℕ → X.G.Kf),
    polDel X Kc j (∏ b, rename (emX X j b) (srcN X j b (x b))) = ∏ b, tgtD X Kc j b (x b)

def XB : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc] [Infinite Kc] (j : ℕ)
    (La : X.Lt j) (La' : X.Lt (j + 1)) (φ : Frm X j La La') (P : DA X Kc j) (f : MvPowerSeries (X.ZA j) Kc)
    (l : XspC (X.Pj (j + 1)) Kc →ₗ[Kc] Kc) (R : MvPolynomial (X.ZA j) Kc),
    (∀ d0 : X.ZA j → Kc, eval d0 R = l (evD X Kc j (fun y => ∑ z, bc Kc φ z y * d0 z) P)) →
      l (pairD X Kc j P (linSub (bc Kc φ) f)) = ∑ n ∈ R.support, derAt X Kc j n f * coeff n R

def TransposedFrameImageBlockwise : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc] (j : ℕ)
    (La : X.Lt j) (La' : X.Lt (j + 1)) (φ : Frm X j La La') (d0 : X.ZA j → Kc) (b : BX X),
    dM X Kc j b (fun y => ∑ z, bc Kc φ z y * d0 z) = (Pf Kc φ b.1 b.2).transpose * dM X Kc j b d0 * Qf Kc φ b.1 b.2

def XC : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ) (b : BX X)
    (x : Fin (NJ X j) → ℕ → X.G.Kf) (d0 : X.ZA j → Kc),
    evD X Kc j d0 (tgtD X Kc j b x) =
      rename (emX X (j + 1) b) (tgtN X Kc j b (mulC (dM X Kc j b d0).transpose fun a i => algebraMap X.G.Kf Kc (x a i)))

def XG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ) (I : X.ColCh j) (i0 : X.Pl → ℕ)
    (f : MvPowerSeries (X.ZA j) Kc) (x : X.FrI j → Kc),
    ∑ n ∈ (map (eval₂Hom (Int.castRingHom Kc) x) (X.PI j I i0)).support,
        derAt X Kc j n f * coeff n (map (eval₂Hom (Int.castRingHom Kc) x) (X.PI j I i0)) =
      eval x (applyD (X.PI j I i0) f)

end Formalism.L2.PairingIndexBounds.Ent
end
end

section
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Defs

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def DgX (K' : Type) [Field K'] (j : ℕ) (i0 : X.Pl → ℕ) (v : X.Pl) : Matrix (Fin (NJ X (j + 1))) (Fin (NJ X (j + 1))) K' :=
  Matrix.diagonal fun a => if a.val < i0 v then (p : K')⁻¹ else 1

variable (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc]

def numericalIdentityScalar (j : ℕ) (g : ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
    (g' : ∀ v : X.Pl, Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)) (i0 : X.Pl → ℕ) : Kc :=
  ∏ b : BX X, if IsOddPos b.2 then
      (algebraMap X.G.Kf Kc (mF X j b (g b.1)).det) ^ (-(cX X j b : ℤ)) *
        (algebraMap X.G.Kf Kc (mF X (j + 1) b (g' b.1) * DgX X X.G.Kf j i0 b.1).det) ^ (cX X j b)
    else (algebraMap X.G.Kf Kc (mF X j b (g b.1)).det) ^ (eX X j b) *
      (p : Kc) ^ (-((∑ k : Fin (cX X j b), min (X.colHt b.1 (j + 1) b.2 k.val) (i0 b.1) : ℕ) : ℤ))

end Defs

def PairingSeriesLinearForm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] [Infinite Kc] (j : ℕ)
    (P : DA X Kc j) (f : MvPowerSeries (X.ZA j) Kc) (l : XspC (X.Pj (j + 1)) Kc →ₗ[Kc] Kc) (R : MvPolynomial (X.ZA j) Kc),
    (∀ d0 : X.ZA j → Kc, eval d0 R = l (evD X Kc j d0 P)) →
      l (pairD X Kc j P f) = ∑ n ∈ R.support, derAt X Kc j n f * coeff n R

def XMid : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc] [CharZero Kc] (j : ℕ)
    (La : X.Lt j) (La' : X.Lt (j + 1)) (φ : Frm X j La La') (i0 : X.Pl → ℕ)
    (I : ∀ (b : BX X) (k : Fin (cX X j b)), Fin (szT X j b k) → Fin (NJ X (j + 1))), (∀ b k, Function.Injective (I b k)) →
    ∃ (Ist : X.ColCh j) (ε : Kc), (ε = 1 ∨ ε = -1) ∧
      ∀ (f : MvPowerSeries (X.ZA j) Kc) (x : X.FrI j → X.G.Kf),
        fockR (delF X Kc j (∏ b, rename (emX X j b) (rowAct X.G.Kf (mF X j b ((φ.g b.1)⁻¹ : GL _ _))
            (evX (fun s => x (xmX X j b s)) (HgX X X.G.Kf j b)))) (linSub (bc Kc φ) f))
          (map (algebraMap X.G.Kf Kc) (∏ b, rename (emX X (j + 1) b)
            (rowAct X.G.Kf (mF X (j + 1) b (φ.g' b.1) * DgX X X.G.Kf j i0 b.1).transpose
              (bideterminant X.G.Kf (szT X j b) (szT_le X j b) (I b))))) =
        ε * numericalIdentityScalar X Kc j (fun v => φ.g v) (fun v => φ.g' v) i0 * (∏ b, cN Kc (nuT X j b)) *
          eval (fun t => algebraMap X.G.Kf Kc (x t)) (applyD (X.PI j Ist i0) f)

def XSpanN : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] [CharZero Kc] (j : ℕ)
    (x : ∀ b : BX X, Fin (NJ X j) → ℕ → X.G.Kf) (f : MvPowerSeries (X.ZA j) Kc),
    delF X Kc j (∏ b, rename (emX X j b) (srcN X j b (x b))) f ∈
      Submodule.span Kc {z | ∃ F : BX X → MvPolynomial (Fin (NJ X (j + 1)) × Fin (NJ X (j + 1))) X.G.Kf,
        (∀ b, F b ∈ dualWeyl X.G.Kf (NJ X (j + 1)) (NJ X (j + 1)) (nuT X j b)) ∧
          z = map (algebraMap X.G.Kf Kc) (∏ b, rename (emX X (j + 1) b) (F b))}

def XUnit : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (Oc : Subring Kc),
    (∀ o : X.G.O, algebraMap X.G.Kf Kc (algebraMap X.G.O X.G.Kf o) ∈ Oc) → (p : Kc) ≠ 0 →
    ∀ (j : ℕ) (L : (X.Pj j).Tup) (L'' : (X.Pj (j + 1)).Tup)
      (g : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) (g' : ∀ v : X.Pl, GL (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)),
      (∀ v, X.latAt v j L = colSpan (X.G.P.W v) (g v : Matrix _ _ (X.G.P.Qq v))) →
      (∀ v, X.latAt v (j + 1) L'' = colSpan (X.G.P.W v) (g' v : Matrix _ _ (X.G.P.Qq v))) →
      ∀ i0 : X.Pl → ℕ, (∀ v, i0 v ≤ X.G.P.r) →
        algebraMap X.G.Kf Kc ((∏ v : X.Pl, (p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) (j + 1) (i0 v))) *
            ((∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v j L)) *
              (∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v (j + 1) L''))⁻¹) *
            sX X j (fun v => g v) *
            (∏ b : BX X, (mF X (j + 1) b (g' b.1) * DgX X X.G.Kf j i0 b.1).det ^ (-(eJ X (j + 1) b.1 b.2)))⁻¹) *
          numericalIdentityScalar X Kc j (fun v => g v) (fun v => g' v) i0 ∈ Oc

def XEdge : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (j : ℕ) (L' L'' : (X.Pj (j + 1)).Tup) (i0 : X.Pl → ℕ),
    (X.Pj (j + 1)).IsLatTup L' →
    (∀ v' : Fin (X.Pj (j + 1)).nV, (i0 (X.vB (j + 1) v') = 0 ∧ L'' v' = L' v') ∨
      (1 ≤ i0 (X.vB (j + 1) v') ∧ IsEdge p ((X.Pj (j + 1)).n' v') (i0 (X.vB (j + 1) v')) ⟨L'' v', L' v'⟩)) →
    ∃ g' h' : ∀ v : X.Pl, GL (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v),
      (∀ v, X.latAt v (j + 1) L'' = colSpan (X.G.P.W v) (g' v : Matrix _ _ (X.G.P.Qq v))) ∧
      (∀ v, X.latAt v (j + 1) L' = colSpan (X.G.P.W v) (h' v : Matrix _ _ (X.G.P.Qq v))) ∧
      ∀ b : BX X, mF X (j + 1) b (h' b.1) = mF X (j + 1) b (g' b.1) * DgX X X.G.Kf j i0 b.1

end Formalism.L2.PairingIndexBounds.Ent
end
end
