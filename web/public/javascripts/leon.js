var editor = null;

function appendError(title, msg) {
    alert(title+": "+msg)
}

function loadExample(kind, prefix) {
    var value = $("#example-loader-"+kind).val()

    if (value) { 
        $.ajax({
          url: prefix+'/ajax/getExample/'+value,
          dataType: "json",
          success: function(data, textStatus, jqXHR) {
            if (data.status == "success") {
                editor.setValue(data.code);
                editor.selection.clearSelection();
                editor.gotoLine(0);
            } else {
                appendError("Loading example failed :(", data.errormsg)
            }
          },
          error: function(jqXHR, textStatus, errorThrown) {
            appendError("Loading example failed :(", errorThrown)
          }
        });
    }
}

$(document).ready(function() {
    editor = ace.edit("codebox");
    editor.getSession().setMode("ace/mode/scala");
    editor.getSession().setUseWrapMode(true);


    $("#tabs a").click(function() {
        activateTab($(this).attr("href"));
    });

    var hash = window.location.hash

    if (hash == "") {
        activateTab("#verification");
    } else {
        activateTab(hash);
    }
});


function activateTab(tab) {

    $("#tabs a").each(function() {
        var wh = $(this).attr("href").substr(1);
        if ($(this).attr("href") == tab) {
            $(this).addClass("active");
            $("#tab-"+wh).show();
            $("#leon-mode").val(wh);
        } else {
            $(this).removeClass("active");
            $("#tab-"+wh).hide();
        }
    });
}
