module Iopt = Term_indexing.Int_option

let of_int_fail =
  Alcotest.test_case "of_int_fail" `Quick (fun () ->
      Alcotest.(
        check_raises
          "of_int_fail"
          (Invalid_argument "Int_option.of_int")
          (fun () -> ignore (Iopt.of_int max_int))))

let iopt_pp =
  Alcotest.test_case "pp" `Quick (fun () ->
      Alcotest.(
        check
          string
          "pp_some"
          (Format.asprintf "%a" Iopt.pp (Iopt.of_int 42))
          "some 42") ;
      Alcotest.(
        check string "pp_none" (Format.asprintf "%a" Iopt.pp Iopt.none) "none"))

let unsafe_to_int =
  Alcotest.test_case "unsafe_to_int" `Quick (fun () ->
      Alcotest.(
        check int "unsafe_to_int" (Iopt.unsafe_to_int (Iopt.of_int 42)) 42))

let () =
  let open Alcotest in
  run
    "Int_option"
    [ ("of_int_fail", [of_int_fail]);
      ("pp", [iopt_pp]);
      ("unsafe_to_int", [unsafe_to_int]) ]
