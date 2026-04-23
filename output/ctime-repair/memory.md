# ctime-repair

- Active proof target: `rocq-brick-libstdcpp/test/ctime/proof.v`
- Current reproduced failure from `dune build ./test/ctime/proof.vo`:
  - non-fatal missing-spec diagnostics for POD repro lemmas via `verify?`
  - earlier fatal proof failure at `test_mktime_ptr_ok`
- Live replay in `dune rocq top test/ctime/proof.v` found the wrapper-spec issue:
  - using `\pre{q tm_in}` was still too strong and left a half-fraction ownership mismatch
  - the correct wrapper statement uses `\prepost{q tm_in} tm_p |-> tmR q tm_in`
    and makes the explicit post ask only for the pure `mktime_result` witness plus
    `tm_p |-> tmR (cQp.scale (1 / 2) q) tm_out`
  - under that statement, `verify_spec; go.` leaves only
    `∃ t0 : time_t_model, [| mktime_result tm_in t t0 |]`
  - `iExists _. go.` closes the proof
- Current repair choice:
  - keep the `test_mktime_ptr_ok` proof as
    `verify_spec. go. iExists _. go. Qed.`
