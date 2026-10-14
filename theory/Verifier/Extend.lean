/-
The match of a proof file with its specification (milestone V6): a reference matcher
proved sound for `env.extend`, and the end-to-end theorem — a proof file that the
reference verifier accepts and that the matcher finds to extend the specification
proves the specification (`env.proof`).
-/
import Verifier.Check

namespace Verifier

open mm0

deriving instance DecidableEq for sort_data
deriving instance DecidableEq for binder
deriving instance DecidableEq for sexpr
deriving instance DecidableEq for decl

/-- The file's declaration `d2` gives a value to the specification's abstract def `d1`. -/
def abstractOf : decl → decl → Bool
  | .defn id a r none, .defn id' a' r' _ => decide (id = id' ∧ a = a' ∧ r = r')
  | _, _ => false

def isSkippable : decl → Bool
  | .defn .. => true
  | .thm .. => true
  | _ => false

/-- The reference matcher, on the two environments reversed (the last declaration
first); `L` are the file's local flags, reversed. A local declaration of the file is
skipped (a def or a theorem); every other one is the specification's, or gives a value
to the specification's abstract def. -/
def extendRev : List decl → List decl → List Bool → Bool
  | [], [], [] => true
  | R1, d :: R2, true :: L => isSkippable d && extendRev R1 R2 L
  | d1 :: R1, d2 :: R2, false :: L => (decide (d1 = d2) || abstractOf d1 d2) && extendRev R1 R2 L
  | _, _, _ => false

theorem extendRev_sound : ∀ {R1 R2 : List decl} {L : List Bool}, extendRev R1 R2 L = true →
    env.extend R1.reverse R2.reverse
  | [], [], [], _ => env.extend.nil
  | R1, d :: R2, true :: L, h => by
    simp only [extendRev, Bool.and_eq_true] at h
    obtain ⟨hs, h⟩ := h
    have ih := extendRev_sound h
    rw [List.reverse_cons]
    cases d with
    | defn id a r o => exact env.extend.defn_skip ih
    | thm a hs' r => exact env.extend.thm_skip ih
    | _ => simp [isSkippable] at hs
  | d1 :: R1, d2 :: R2, false :: L, h => by
    simp only [extendRev, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨hd, h⟩ := h
    have ih := extendRev_sound h
    rw [List.reverse_cons, List.reverse_cons]
    rcases hd with rfl | hab
    · exact env.extend.keep ih
    · cases d1 with
      | defn id a r o =>
        cases o with
        | none =>
          cases d2 with
          | defn id' a' r' o' =>
            simp only [abstractOf, decide_eq_true_eq] at hab
            obtain ⟨rfl, rfl, rfl⟩ := hab
            exact env.extend.defn_def ih
          | _ => simp [abstractOf] at hab
        | some _ => simp [abstractOf] at hab
      | _ => simp [abstractOf] at hab
  | [], [], _ :: _, h => by simp [extendRev] at h
  | [], _ :: _, false :: _, h => by simp [extendRev] at h
  | _ :: _, [], _, h => by simp [extendRev] at h
  | _ :: _, _ :: _, [], h => by simp [extendRev] at h
  | [], _ :: _, [], h => by simp [extendRev] at h

/-- **The end-to-end theorem** (milestone V6): a decoded proof file that the reference
verifier accepts, whose environment the matcher finds to extend the specification `S`,
proves `S` — `env.proof` of the formal semantics. -/
theorem spec_proved {f : File} {S E : env} {L : List Bool} (hc : checkFile f = true) (hE : toEnv f = some E)
    (hx : extendRev S.reverse E.reverse L = true) : env.proof S := by
  obtain ⟨E', hE', hp⟩ := checkFile_correct hc
  rw [hE] at hE'
  simp only [Option.some.injEq] at hE'
  subst hE'
  have := extendRev_sound hx
  rw [List.reverse_reverse, List.reverse_reverse] at this
  exact ⟨E, this, hp⟩

/-- **Validity** (milestone V3b): with the well-formedness of the proof file's
environment, `mm0.mm0`'s `ValidEnv S` but for `Env S`, the specification's own
well-formedness, which is the front end's: some well-formed environment extends `S`
and proves every theorem of it. -/
theorem spec_valid {f : File} {S E : env} {L : List Bool} (hc : checkFile f = true) (hE : toEnv f = some E)
    (hx : extendRev S.reverse E.reverse L = true) : ∃ E', env.ok E' ∧ env.extend S E' ∧ env.proof' E' := by
  obtain ⟨E', hE', hok, hp⟩ := file_valid (checkFile_sound hc)
  rw [hE] at hE'
  simp only [Option.some.injEq] at hE'
  subst hE'
  have := extendRev_sound hx
  rw [List.reverse_reverse, List.reverse_reverse] at this
  exact ⟨E, hok, this, hp⟩

end Verifier
