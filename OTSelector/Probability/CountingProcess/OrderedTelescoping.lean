import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Telescoping along a finite ordered event set

For a finite set of totally ordered events, the state immediately before an event is the initial
integer plus the increments of all strictly earlier events.  Summing the one-event changes of an
arbitrary test function telescopes to its total change.  This is the deterministic ordering lemma
needed before specializing events to the two families of attained counting-process jumps.
-/

open scoped BigOperators

namespace OTSelector.CountingProcess

/-- Integer state immediately before `x`, obtained from all events in `s` strictly before `x`. -/
def orderedPriorState {E : Type*} [LinearOrder E]
    (s : Finset E) (step : E → ℤ) (k₀ : ℤ) (x : E) : ℤ :=
  k₀ + ∑ y ∈ s.filter (fun y ↦ y < x), step y

/-- Exact telescoping identity for a finite totally ordered family of integer jumps. -/
theorem sum_ordered_increment_eq
    {E : Type*} [LinearOrder E] (s : Finset E) (step : E → ℤ)
    (f : ℤ → ℝ) (k₀ : ℤ) :
    ∑ x ∈ s,
        (f (orderedPriorState s step k₀ x + step x) -
          f (orderedPriorState s step k₀ x)) =
      f (k₀ + ∑ x ∈ s, step x) - f k₀ := by
  induction s using Finset.induction_on_min generalizing k₀ with
  | empty => simp [orderedPriorState]
  | @insert a s ha_min ih =>
      have ha_not_mem : a ∉ s := by
        intro ha
        exact (lt_irrefl a) (ha_min a ha)
      have hbefore_a : (insert a s).filter (fun y ↦ y < a) = ∅ := by
        ext y
        constructor
        · intro hy
          rcases Finset.mem_filter.mp hy with ⟨hys, hya⟩
          rcases Finset.mem_insert.mp hys with hy | hy
          · exact ((lt_irrefl a) (hy ▸ hya)).elim
          · exact ((not_lt_of_ge (ha_min y hy).le) hya).elim
        · intro hy
          simp at hy
      have hbefore_mem : ∀ x ∈ s,
          (insert a s).filter (fun y ↦ y < x) =
            insert a (s.filter (fun y ↦ y < x)) := by
        intro x hx
        rw [Finset.filter_insert]
        simp only [ha_min x hx, ite_true]
      have hprior_a : orderedPriorState (insert a s) step k₀ a = k₀ := by
        simp [orderedPriorState, hbefore_a]
      have hprior_mem : ∀ x ∈ s,
          orderedPriorState (insert a s) step k₀ x =
            orderedPriorState s step (k₀ + step a) x := by
        intro x hx
        rw [orderedPriorState, orderedPriorState, hbefore_mem x hx]
        rw [Finset.sum_insert]
        · ring
        · intro ha_filter
          exact ha_not_mem (Finset.mem_filter.mp ha_filter).1
      rw [Finset.sum_insert ha_not_mem]
      simp only [hprior_a]
      have hrest :
          ∑ x ∈ s,
              (f (orderedPriorState (insert a s) step k₀ x + step x) -
                f (orderedPriorState (insert a s) step k₀ x)) =
            f ((k₀ + step a) + ∑ x ∈ s, step x) - f (k₀ + step a) := by
        calc
          ∑ x ∈ s,
                (f (orderedPriorState (insert a s) step k₀ x + step x) -
                  f (orderedPriorState (insert a s) step k₀ x)) =
              ∑ x ∈ s,
                (f (orderedPriorState s step (k₀ + step a) x + step x) -
                  f (orderedPriorState s step (k₀ + step a) x)) := by
                    apply Finset.sum_congr rfl
                    intro x hx
                    rw [hprior_mem x hx]
          _ = f ((k₀ + step a) + ∑ x ∈ s, step x) - f (k₀ + step a) :=
            ih (k₀ := k₀ + step a)
      rw [hrest, Finset.sum_insert ha_not_mem]
      have harg :
          k₀ + (step a + ∑ x ∈ s, step x) =
            (k₀ + step a) + ∑ x ∈ s, step x := by
        ring
      rw [harg]
      ring

/-- Time-indexed form of `sum_ordered_increment_eq`.  Injectivity is precisely the exclusion of
simultaneous events; it lets the event order be pulled back from the time order without an
arbitrary tie-breaking convention. -/
theorem sum_timeOrdered_increment_eq
    {E Time : Type*} [Fintype E] [DecidableEq E] [LinearOrder Time]
    (time : E → Time) (htime : Function.Injective time) (step : E → ℤ)
    (f : ℤ → ℝ) (k₀ : ℤ) :
    ∑ x : E,
        (f (k₀ + (∑ y ∈ (Finset.univ.filter fun y : E ↦ time y < time x), step y) +
              step x) -
          f (k₀ + ∑ y ∈ (Finset.univ.filter fun y : E ↦ time y < time x), step y)) =
      f (k₀ + ∑ x : E, step x) - f k₀ := by
  let _ : LinearOrder E := LinearOrder.lift' time htime
  change
    ∑ x : E,
        (f (k₀ + (∑ y ∈ (Finset.univ.filter fun y : E ↦ y < x), step y) + step x) -
          f (k₀ + ∑ y ∈ (Finset.univ.filter fun y : E ↦ y < x), step y)) =
      f (k₀ + ∑ x : E, step x) - f k₀
  simpa only [orderedPriorState] using
    sum_ordered_increment_eq (Finset.univ : Finset E) step f k₀

/-- Finite-set form using an injective ordered key.  The key may contain a deterministic
tie-breaker; a later no-simultaneous-events theorem can identify key order with strict time order
on the event set actually under consideration. -/
theorem sum_keyOrdered_increment_eq
    {E Key : Type*} [DecidableEq E] [LinearOrder Key]
    (s : Finset E) (key : E → Key) (hkey : Function.Injective key)
    (step : E → ℤ) (f : ℤ → ℝ) (k₀ : ℤ) :
    ∑ x ∈ s,
        (f (k₀ + (∑ y ∈ (s.filter fun y ↦ key y < key x), step y) + step x) -
          f (k₀ + ∑ y ∈ (s.filter fun y ↦ key y < key x), step y)) =
      f (k₀ + ∑ x ∈ s, step x) - f k₀ := by
  let _ : LinearOrder E := LinearOrder.lift' key hkey
  change
    ∑ x ∈ s,
        (f (k₀ + (∑ y ∈ (s.filter fun y ↦ y < x), step y) + step x) -
          f (k₀ + ∑ y ∈ (s.filter fun y ↦ y < x), step y)) =
      f (k₀ + ∑ x ∈ s, step x) - f k₀
  simpa only [orderedPriorState] using sum_ordered_increment_eq s step f k₀

end OTSelector.CountingProcess
