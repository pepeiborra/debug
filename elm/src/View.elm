module View exposing (processCall, view)

import Array exposing (..)
import Dict
import Html exposing (..)
import Html.Attributes exposing (..)
import Html.Events exposing (onClick, onInput)
import List
import Maybe.Extra as Maybe
import Paginate exposing (..)
import Regex exposing (..)
import Set
import String
import Trace exposing (..)
import Tuple exposing (second)
import Types exposing (..)


view : Model -> Html Msg
view model =
    case ( model.trace, router model.location ) of
        ( Result.Err e, _ ) ->
            text e

        ( Result.Ok trace, SelectCall selectedCall ) ->
            viewCall model trace selectedCall


viewCall : Model -> DebugTrace ProcessedCall -> Int -> Html Msg
viewCall model trace selectedCall =
    let
        processedCall =
            Array.get selectedCall trace.calls

        fun =
            processedCall |> Maybe.map (\processedCall -> processedCall.call.callFunction)

        expander : Html msg -> List (Html msg) -> Html msg
        expander top rest =
            details [ attribute "open" "" ] (summary [] [ top ] :: rest)

        section name =
            expander (h2 [ style [ ( "display", "inline-block" ) ] ] [ text name ])
    in
    table [ style [ ( "height", "100%" ), ( "width", "100%" ) ] ]
        [ tr [] [ td [ colspan 3 ] [ h1 [] [ text "Haskell Debugger" ] ] ]
        , tr []
            [ td [ rowspan 3, style [ ( "width", "25%" ), ( "padding-right", "40px" ) ] ]
                [ h2 [] [ text "Functions" ]
                , viewCallList model trace
                ]
            , td []
                [ section "Source"
                    [ ul [ id "function-source" ]
                        [ viewSource trace (Maybe.map (\x -> x.call) processedCall) ]
                    ]
                ]
            ]
        , tr []
            [ td []
                [ section "Variables"
                    [ viewVariables trace (Maybe.map (\x -> x.call) processedCall) ]
                ]
            ]
        , tr [ id "function-depends-section" ]
            [ td []
                [ section "Call stack"
                    [ viewCallStack trace (Maybe.map (\x -> x.call) processedCall) ]
                ]
            ]
        ]


viewCallList : Model -> DebugTrace ProcessedCall -> Html Msg
viewCallList model trace =
    let
        callsPerPageSelector =
            div [ class "calls-per-page" ]
                [ text "Showing"
                , let
                    current =
                        Paginate.itemsPerPage model.filteredCalls
                  in
                  select [ onInput ChangeCallPageSize ]
                    ([ 10, 20, 30, 40, 50, 100, 1000 ]
                        |> List.map
                            (\n ->
                                option [ value (toString n), selected (current == n) ] [ text (toString n) ]
                            )
                    )
                , text "calls per page"
                ]

        prevButton =
            button [ onClick (CallPage Prev), disabled <| Paginate.isFirst model.filteredCalls ] [ text "<" ]

        nextButton =
            button [ onClick (CallPage Next), disabled <| Paginate.isLast model.filteredCalls ] [ text ">" ]

        numButtons =
            span [] <| boundedPager 3 pagerButtonView model.filteredCalls

        pagerButtonView index isActive =
            button
                [ style
                    [ ( "font-weight"
                      , if isActive then
                            "bold"
                        else
                            "normal"
                      )
                    ]
                , onClick <| CallPage (GoTo index)
                ]
                [ text <|
                    toString index
                        ++ (if isActive then
                                " of " ++ toString (Paginate.totalPages model.filteredCalls)
                            else
                                ""
                           )
                ]

        functionNameSelector =
            select [ id "function-drop", style [ ( "width", "100%" ) ], onInput SelectFunction ]
                (option [] [ text "(All)" ]
                    :: (trace.functions |> Array.map (\x -> x.name) |> Array.toList |> Set.fromList |> Set.toList |> List.map (\x -> option [] [ text x ]))
                )

        nameFilterInput =
            input
                [ id "function-text"
                , style [ ( "margin-top", "5px" ), ( "width", "100%" ) ]
                , type_ "text"
                , placeholder "Filter (using regex)"
                , onInput CallFilter
                ]
                []

        callView ( i, c ) =
            li [] [ viewCallLink i c.rendered ]
    in
    div [] <|
        [ functionNameSelector
        , nameFilterInput

        {- , callsPerPageSelector -}
        , prevButton
        , numButtons
        , nextButton
        ]
            ++ [ ul [] (List.map callView <| Paginate.page model.filteredCalls) ]


{-| Used to build a bounded list of page numbers centered around the current page
-}
boundedPager : Int -> (Int -> Bool -> b) -> PaginatedList a -> List b
boundedPager radius f p =
    let
        center =
            currentPage p

        canStart =
            Basics.max 1 (center - radius)

        canEnd =
            Basics.min (totalPages p) (center + radius)

        start =
            Basics.max 1 (canEnd - radius * 2)

        end =
            Basics.min (totalPages p) (canStart + radius * 2)
    in
    List.range start end |> List.map (\i -> f i (i == center))


viewCallLink : Int -> Html Msg -> Html Msg
viewCallLink index rendered =
    a [ class "call-link", href ("#call/" ++ toString index) ] [ rendered ]


viewVariables : DebugTrace a -> Maybe CallData -> Html Msg
viewVariables trace call =
    case call of
        Nothing ->
            text "Corrupt trace: no call"

        Just call ->
            ul [ id "function-variables" ]
                (case findCallDetails trace call of
                    Just ( res, vals ) ->
                        li [] [ pre [] (renderSource (\_ -> Nothing) <| "$result = " ++ res) ]
                            :: List.map
                                (\( n, v ) ->
                                    li [] [ pre [] (renderSource (\_ -> Nothing) (n ++ " = " ++ v)) ]
                                )
                                vals

                    _ ->
                        []
                )


viewCallStack : DebugTrace ProcessedCall -> Maybe CallData -> Html Msg
viewCallStack trace call =
    case call of
        Nothing ->
            text "Corrupt trace: no call"

        Just call ->
            case getCallStackUpwards trace call of
                Result.Err e ->
                    text e

                Result.Ok callstack ->
                    let
                        upwards =
                            List.foldl buildCallStackList (\k -> ul [] [ k ]) (List.reverse callstack)

                        descendants =
                            call.callDepends |> List.map (\i -> ( i, Array.get i trace.calls |> Maybe.map (\x -> x.rendered) |> Maybe.withDefault (text "Corrupt trace") ))

                        downwards =
                            li [ id "function-depends-current" ]
                                [ (processCall trace call).rendered
                                , ul [] (descendants |> List.map (\x -> li [] [ uncurry viewCallLink x ]))
                                ]
                    in
                    upwards downwards


viewSource : DebugTrace a -> Maybe CallData -> Html msg
viewSource trace call =
    case call of
        Nothing ->
            text "Corrupt trace: no call"

        Just call ->
            pre [] (renderSource (getArg trace call) call.callFunction.source)


renderSource : (String -> Maybe String) -> String -> List (Html msg)



--renderSource _ src = [text src]


renderSource getArg =
    let
        loop acc src =
            case find (AtMost 1) hsLexer src of
                [] ->
                    acc

                { match } :: _ ->
                    case match of
                        "" ->
                            acc

                        "where" ->
                            loop (span [ class "hs-keyword" ] [ text "where" ] :: acc) (String.dropLeft 5 src)

                        "=" ->
                            loop (span [ class "hs-equals" ] [ text "=" ] :: acc) (String.dropLeft 1 src)

                        _ ->
                            let
                                it =
                                    case String.indexes match symbols of
                                        _ :: _ ->
                                            span [ class "hs-keyglyph" ] [ text match ]

                                        [] ->
                                            case getArg match of
                                                Just arg ->
                                                    abbr [ title arg ] [ text match ]

                                                Nothing ->
                                                    text match
                            in
                            loop (it :: acc) (String.dropLeft (String.length match) src)
    in
    loop [] >> List.reverse


getArg :
    DebugTrace a
    -> CallData
    -> String
    -> Maybe String
getArg trace call arg =
    Dict.get arg call.callLocals
        |> Maybe.andThen
            (\ix ->
                Array.get ix trace.variables
            )


hsLexer : Regex
hsLexer =
    regex """[a-zA-Z][a-zA-Z0-9]+|[\x0D
]|."""


symbols : String
symbols =
    """->:=()[]"""


buildCallStackList : ( Int, Html Msg ) -> (Html Msg -> b) -> Html Msg -> b
buildCallStackList call parent k =
    parent <| li [] [ uncurry viewCallLink call, ul [] [ k ] ]


getCallStackUpwards : DebugTrace ProcessedCall -> CallData -> Result String (List ( Int, Html Msg ))
getCallStackUpwards trace call =
    case call.callParents of
        [ i ] ->
            Array.get i trace.calls |> Result.fromMaybe "Corrupt trace" |> Result.andThen (\p -> getCallStackUpwards trace p.call |> Result.map (\x -> ( i, p.rendered ) :: x))

        [] ->
            Result.Ok []

        pp ->
            Result.Err <| "Unexpected: more than one parents for a call: " ++ toString pp


{-| Returns a tuple of the result and the local values
-}
findCallDetails : DebugTrace a -> CallData -> Maybe ( String, List ( String, String ) )
findCallDetails trace call =
    (call.callFunction.result :: call.callFunction.arguments)
        |> List.map
            (\arg ->
                case Dict.get arg call.callLocals of
                    Nothing ->
                        Just ( arg, "_" )

                    Just valueIx ->
                        Array.get valueIx trace.variables |> Maybe.map (\x -> ( arg, x ))
            )
        |> Maybe.combine
        |> Maybe.map
            (\vv ->
                case vv of
                    ( _, res ) :: args ->
                        ( res, args )

                    _ ->
                        ( "_", [] )
            )


renderCall : DebugFunction -> List ( String, String ) -> String -> Html arg
renderCall callFunction args res =
    div [ class "render-call" ] <|
        text callFunction.name
            :: List.filterMap
                (\( name, v ) ->
                    if String.startsWith "$arg" name then
                        Just (printArg v)
                    else
                        Nothing
                )
                args
            ++ [ span [ class "hs-equals" ] [ text " = " ]
               , printArg res
               ]


printArg : String -> Html arg
printArg arg =
    if String.length arg > 20 then
        abbr [ class "render-arg", title arg ]
            [ div [] (renderSource (\_ -> Nothing) (String.left 20 arg) ++ [ span [ class "hs-keyglyph" ] [ text ".." ] ]) ]
    else
        span [ class "render-arg" ] (renderSource (\_ -> Nothing) arg)


mkSearchString : DebugFunction -> List ( String, String ) -> String -> String
mkSearchString callFunction args res =
    String.join " " <| callFunction.name :: List.map second args ++ [ " = ", res ]


processCall : DebugTrace a -> CallData -> ProcessedCall
processCall tr call =
    case findCallDetails tr call of
        Nothing ->
            { call = call, rendered = errorSpan "Invalid trace: null ref", searchString = "" }

        Just ( res, args ) ->
            { call = call, rendered = renderCall call.callFunction args res, searchString = mkSearchString call.callFunction args res }


errorSpan : String -> Html msg
errorSpan msg =
    span [ class "error" ] [ text msg ]
