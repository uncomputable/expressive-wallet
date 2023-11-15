open Strategy

let show_usage () =
  print_endline "Usage:";
  print_endline "wallet <target> [<denominations>]";
  print_endline "\nArguments:";
  print_endline "<target>        target amount";
  print_endline "<denominations> list of coin denominations";
  print_endline "                default: 1, 2, 5, 10, 20, 50";
  exit 0

type cli = {
  target: int;
  denominations: int list;
}

let parse_target str =
  try
    let n = int_of_string str in
    if n < 0 then
      (Printf.eprintf "Target must be greater equal zero\n"; exit 1);
    n
  with Failure _ -> Printf.eprintf "Invalid target: %s\n" str; exit 1

let parse_coin str =
  try int_of_string str
  with Failure _ -> Printf.eprintf "Invalid coin: %s\n" str; exit 1

let parse_list str =
  str
  |> String.split_on_char ','
  |> List.map String.trim
  |> List.map parse_coin
  |> List.sort compare
  |> List.rev

let parse args =
  if Array.length args < 2 then
    show_usage ();

  if args.(1) = "-h" || args.(1) = "--help" then
    show_usage ();

  let target = parse_target args.(1) in

  let denominations =
    if Array.length args > 2 then
      parse_list args.(2)
    else
      [50; 20; 10; 5; 2; 1]
  in

  { target; denominations }

let () =
  let cli = parse Sys.argv in
  let wallet = strategy cli.denominations cli.target in
  Printf.printf "Target: %d\n" cli.target;
  Printf.printf "Denominations: %s\n"
    (String.concat ", " (List.map string_of_int cli.denominations));
  Printf.printf "\nWallet: %s\n"
    (String.concat ", " (List.map string_of_int wallet));

