abstract Face = {

flags startcat = Message ;

cat
Message ; Person ; Object ; Number ;
fun
Have : Person -> Number -> Object -> Message ; -- p has n o’s
Like : Person -> Object -> Message ; -- p likes o
You : Person ;
Friend, Invitation : Object ;
One, Two, Hundred : Number ;
}